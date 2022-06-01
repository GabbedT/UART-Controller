// MIT License
//
// Copyright (c) 2021 Gabriele Tripi
// 
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
// 
// The above copyright notice and this permission notice shall be included in all
// copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.
// ------------------------------------------------------------------------------------
// ------------------------------------------------------------------------------------
// FILE NAME : receiver.sv
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// ------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : This module contains the receiver of the uart. It is composed by
//               a main FSM and a FIFO buffer. The FSM takes care of the transaction
//               timing and interrupt assertion. A threshold can be set and will be 
//               useful only in data stream mode, the receiver will interrupt once
//               the fifo has receiven a certain amount of data instead of every data 
//               byte. The configuration request start by receiving 3 SYN character 
//               from the master, once this happens, the receiver expects the RX line
//               to be low for 10ms, once this finishes `config_req_slv_o` is asserted, 
//               the master sends another SYN character to reset the SYN counter to 0.   
// ------------------------------------------------------------------------------------
// KEYWORDS : PARAMETERS, RX FIFO, DATAPATH, FSM LOGIC, ASSERTIONS
// ------------------------------------------------------------------------------------

import UART_pkg::*;
import fsm_pkg::*;

module receiver (
    input  logic         clk_i,
    input  logic         rst_n_i,
    input  logic         enable,
    input  logic         ov_baud_rt_i,
    input  logic         rx_i,
    input  logic         rx_fifo_read_i,
    input  logic         req_ackn_i,
    input  logic [5:0]   threshold_i,
    input  logic         rx_data_stream_mode_i,
    input  logic [1:0]   data_width_i,
    input  logic [1:0]   stop_bits_number_i,
    input  logic [1:0]   parity_mode_i,
    
    output logic         rx_fifo_full_o,
    output logic         rx_fifo_empty_o,
    output logic         config_req_slv_o,
    output logic         overrun_error_o,
    output logic         frame_error_o,
    output logic         parity_o,
    output logic         rx_done_o,
    output logic         rxd_rdy_o,
    output logic [7:0]   data_rx_o,
    output logic         rx_idle_o
);

//--------------//
//  PARAMETERS  //
//--------------//

    /* Index in fifo data */
    localparam FRAME = 9;
    localparam OVERRUN = 10;
    localparam PARITY_BIT = 8;


//-----------//
//  RX FIFO  //
//-----------//

    /* Reset fifo if a configuration request is received */
    logic fifo_rst_n;

    /* Interface declaration, 8 data bits, 2 error bits and 1 parity bit */
    sync_fifo_interface #(11) fifo_if(clk_i);

    assign fifo_if.read_i = rx_fifo_read_i;
    assign fifo_if.rst_n_i = rst_n_i & fifo_rst_n; 

    /* FIFO buffer instantiation in FWFT mode */
    sync_FIFO_buffer #(TX_FIFO_DEPTH, 1) tx_fifo (clk_i, fifo_if);

    assign rx_fifo_empty_o = fifo_if.empty_o;


//------------//
//  DATAPATH  //
//------------//

    /* Data received */
    logic [7:0] data_rx[NXT:CRT];

    /* Counter for data oversampling (16 times the baudrate) */
    logic [3:0] counter_16br[NXT:CRT];

    /* Number of data bits received */
    logic [2:0] bits_processed[NXT:CRT];

    /* Number of stop bits received */
    logic stop_bits_cnt[NXT:CRT];

    /* Store parity and stop bits of data received */
    logic parity_bit[NXT:CRT];
    logic stop_bits[NXT:CRT];

    /* Count the amount of consecuteve SYN character received */
    logic [$clog2(SYN_NUMBER) - 1:0] syn_data_cnt[NXT:CRT];

        always_ff @(posedge clk_i or negedge rst_n_i) begin
            if (!rst_n_i) begin
                syn_data_cnt[CRT] <= 2'b0;
            end else begin 
                syn_data_cnt[CRT] <= syn_data_cnt[NXT];
            end
        end 
        
        /* No reset because they are resetted in the FSM combinatorial logic
         * this saves area */
        always_ff @(posedge clk_i or negedge rst_n_i) begin : datapath_register
            data_rx[CRT] <= data_rx[NXT];
            counter_16br[CRT] <= counter_16br[NXT];
            bits_processed[CRT] <= bits_processed[NXT];
            stop_bits_cnt[CRT] <= stop_bits_cnt[NXT];
            parity_bit[CRT] <= parity_bit[NXT];
            stop_bits[CRT] <= stop_bits[NXT];
        end : datapath_register


    /* Counter to determine the amount of time the RX line 
     * stays low during configuration request */
    logic [$clog2(COUNT_1MS) - 1:0] counter_10ms[NXT:CRT];

        always_ff @(posedge clk_i or negedge rst_n_i) begin : ms10_counter
            if (!rst_n_i) begin 
                counter_10ms[CRT] <= 'b0;
            end else begin
                counter_10ms[CRT] <= counter_10ms[NXT];
            end
        end : ms10_counter

        always_comb begin : ms10_counter_logic
            if (rx_i != RX_LINE_IDLE) begin 
                counter_10ms[NXT] = counter_10ms[CRT] + 1'b1;
            end else if (counter_10ms[CRT] == COUNT_1MS) begin 
                counter_10ms[NXT] = 'b0;
            end else begin 
                counter_10ms[NXT] = 'b0;
            end
        end : ms10_counter_logic

  
    /* In data stream mode the device will interrupt if a certain
     * amount of data is received. The counter will go from 0 
     * (empty fifo) to FIFO_DEPTH - 1, if the programmer wants
     * the device to interrupt when fifo is full, then the threshold
     * must be set with the value 0. */
    logic [5:0] fifo_size_cnt[NXT:CRT];

        always_ff @(posedge clk_i or negedge rst_n_i) begin : fifo_size_counter
            if (!rst_n_i) begin 
                fifo_size_cnt[CRT] <= 'b0;
            end else begin 
                fifo_size_cnt[CRT] <= fifo_size_cnt[NXT];
            end 
        end : fifo_size_counter

        always_comb begin : fifo_size_counter_logic
            case ({fifo_if.write_i, fifo_if.read_i})
                /* Writing */
                2'b10: fifo_size_cnt[NXT] = fifo_size_cnt[CRT] + 1'b1;
                /* Reading */
                2'b01: fifo_size_cnt[NXT] = fifo_size_cnt[CRT] - 1'b1;
                /* Both or no operation */
                default: fifo_size_cnt[NXT] = fifo_size_cnt[CRT];
            endcase
        end : fifo_size_counter_logic


    /* Interrupt that assert if the fifo size hit the threshold (in data stream mode)
     * or if data is received (in standard mode) */
    logic rx_rdy_int[NXT:CRT];

        always_ff @(posedge clk_i or negedge rst_n_i) begin : data_ready_interrupt_reg
            if (!rst_n_i) begin 
                rx_rdy_int[CRT] <= 1'b0;
            end else if (!rx_data_stream_mode_i & fifo_if.read_i) begin 
                /* Clear when reading data */
                rx_rdy_int[CRT] <= 1'b0;
            end else if (rx_data_stream_mode_i & fifo_if.empty_o) begin 
                /* Clear only if the fifo is empty */
                rx_rdy_int[CRT] <= 1'b0;
            end else begin 
                rx_rdy_int[CRT] <= rx_rdy_int[NXT];
            end
        end : data_ready_interrupt_reg


    /* Configuration process requested. The request will be asserted
     * when the counter reaches the right value (RX low for 10ms) and
     * deasserted when the request is acknowledged */
    logic cfg_req[NXT:CRT];

        always_ff @(posedge clk_i or negedge rst_n_i) begin 
            if (!rst_n_i) begin 
                cfg_req[CRT] <= 1'b0;
            end else if (req_ackn_i) begin 
                cfg_req[CRT] <= 1'b0;
            end else begin 
                cfg_req[CRT] <= cfg_req[NXT];
            end
        end

    assign config_req_slv_o = cfg_req[CRT];


//-------------//
//  FSM LOGIC  //
//-------------//

    /* FSM current and next state */
    fsm_pkg::receiver_fsm_e state[NXT:CRT];

        always_ff @(posedge clk_i or negedge rst_n_i) begin : fsm_state_register
            if (!rst_n_i) begin 
                state[CRT] <= RX_IDLE;
            end else if (!fifo_rst_n) begin 
                state[CRT] <= RX_IDLE;
            end else begin 
                state[CRT] <= state[NXT];
            end
        end : fsm_state_register


        always_comb begin 

            //------------------//
            //  DEFAULT VALUES  //
            //------------------//

            state[NXT] = state[CRT];
            data_rx[NXT] = data_rx[CRT];
            cfg_req[NXT] = cfg_req[CRT];
            stop_bits[NXT] = stop_bits[CRT];
            parity_bit[NXT] = parity_bit[CRT];
            counter_16br[NXT] = counter_16br[CRT];
            syn_data_cnt[NXT] = syn_data_cnt[CRT];
            stop_bits_cnt[NXT] = stop_bits_cnt[CRT];
            bits_processed[NXT] = bits_processed[CRT];
            
            rx_rdy_int[NXT] = 1'b0;
            rx_done_o = 1'b0;
            rx_idle_o = 1'b0;
            fifo_if.write_i = 1'b0;
            fifo_rst_n = 1'b1;

            case (state[CRT])

                /* 
                 *  The device is waiting for data to arrives.
                 */
                RX_IDLE: begin 
                    stop_bits_cnt[NXT] = 1'b0;
                    stop_bits[NXT] = 1'b0;
                    bits_processed[NXT] = 3'b0;
                    counter_16br[NXT] = 4'b0;
                    parity_bit[NXT] = 1'b0;
                    data_rx[NXT] = 8'b0;

                    rx_idle_o = 1'b1;

                    if ((rx_i != RX_LINE_IDLE) & enable) begin 
                        state[NXT] = (syn_data_cnt[CRT] == SYN_NUMBER) ? RX_CONFIG_REQ : RX_START;
                    end
                end

                /* 
                 *  The device is receiving a configuration request. This state 
                 *  is reached after receiving 3 SYN character. 
                 */
                RX_CONFIG_REQ: begin 
                    syn_data_cnt[NXT] = 'b0;

                    /* Could be a false request, recover from it */
                    if (rx_i == RX_LINE_IDLE) begin 
                        state[NXT] = RX_IDLE;
                    end

                    /* Go in IDLE then wait the request. The master won't initiate
                    * other transaction until the request is acknowledged */
                    if (counter_10ms[CRT] == COUNT_1MS) begin 
                        cfg_req[NXT] = 1'b1;
                        state[NXT] = RX_IDLE;

                        /* Reset fifo only if the request is acknowledged */
                        fifo_rst_n = !req_ackn_i;
                    end
                end

                /* 
                 *  Sample the start bit in T/2 time (T is the bit while the
                 *  bit is stable) to grant maximum signal stability.
                 */
                RX_START: begin 
                    if (ov_baud_rt_i) begin 
                        /* Reach the middle of the bit */
                        if (counter_16br[CRT] == 4'd7) begin 
                            counter_16br[NXT] = 4'b0;
                            state[NXT] = RX_SAMPLE;
                        end else begin 
                            counter_16br[NXT] = counter_16br[CRT] + 1'b1;
                        end
                    end
                end

                /* 
                 *  Sample data bits. Since in the START state the counter stopped
                 *  at half of the bit and then switched state, now every time the
                 *  counter reach T, it is in the middle of the start bit. The LSB
                 *  is received first.
                 */
                RX_SAMPLE: begin 
                    /* Reset stop bits */
                    stop_bits[NXT] = 1'b1;

                    if (ov_baud_rt_i) begin 
                        if (counter_16br[CRT] == 4'd15) begin 
                            counter_16br[NXT] = 4'b0;
                            bits_processed[NXT] = bits_processed[CRT] + 1'b1;

                            /* Place the bit in the MSB of the data register,
                            * in the next clock cycle it will be shifted to 
                            * the right */
                            data_rx[NXT] = {rx_i, data_rx[CRT][7:1]};

                            if (parity_mode_i[1]) begin
                                case (data_width_i) 
                                    DW_5BIT: state[NXT] = (bits_processed[CRT] == 4'd4) ? RX_DONE : RX_SAMPLE;
                                    DW_6BIT: state[NXT] = (bits_processed[CRT] == 4'd5) ? RX_DONE : RX_SAMPLE;
                                    DW_7BIT: state[NXT] = (bits_processed[CRT] == 4'd6) ? RX_DONE : RX_SAMPLE;
                                    DW_8BIT: state[NXT] = (bits_processed[CRT] == 4'd7) ? RX_DONE : RX_SAMPLE;
                                endcase
                            end else begin 
                                case (data_width_i) 
                                    DW_5BIT: state[NXT] = (bits_processed[CRT] == 4'd4) ? RX_PARITY : RX_SAMPLE;
                                    DW_6BIT: state[NXT] = (bits_processed[CRT] == 4'd5) ? RX_PARITY : RX_SAMPLE;
                                    DW_7BIT: state[NXT] = (bits_processed[CRT] == 4'd6) ? RX_PARITY : RX_SAMPLE;
                                    DW_8BIT: state[NXT] = (bits_processed[CRT] == 4'd7) ? RX_PARITY : RX_SAMPLE;
                                endcase
                            end
                        end else begin 
                            counter_16br[NXT] = counter_16br[CRT] + 1'b1;
                        end
                    end 
                end

                /* 
                 *  Sample parity bit. 
                 */
                RX_PARITY: begin 
                    if (ov_baud_rt_i) begin 
                        if (counter_16br[CRT] == 4'd15) begin 
                            counter_16br[NXT] = 4'b0;
                            parity_bit[NXT] = rx_i;
                            state[NXT] = RX_DONE;
                        end else begin 
                            counter_16br[NXT] = counter_16br[CRT] + 1'b1;
                        end
                    end 
                end

                /* 
                 *  During DONE state, the stop bits are detected. During 
                 *  this time the RX line must be stable on IDLE.
                 */
                RX_DONE: begin  
                    /* Raise an interrupt */
                    if (state[NXT] == RX_IDLE) begin
                        if (rx_data_stream_mode_i) begin
                            if (threshold_i != 'b0) begin 
                                /* Interrupt if fifo size is greater or equal the threshold value */
                                rx_rdy_int[NXT] = (fifo_size_cnt[CRT] >= threshold_i);
                            end else if (threshold_i == 'b0) begin 
                                /* Interrupt only if fifo is full in the next clock cycle (the counter ) */
                                rx_rdy_int[NXT] = (fifo_size_cnt[CRT] == 6'b1);    
                            end 
                        end else begin 
                            rx_rdy_int[NXT] = 1'b1;
                        end
                    end


                    if (ov_baud_rt_i) begin
                        if (counter_16br[CRT] == 4'd15) begin
                            /* AND the rx line with the stop bits so if in the
                             * previous cycle the stop bits wasn't detected 
                             * (logic 0) then the information doesn't get lost */
                            stop_bits[NXT] = stop_bits[CRT] & rx_i;

                            case (stop_bits_number_i)
                                SB_2BIT: begin 
                                    stop_bits_cnt[NXT] = 1'b1;
                                    state[NXT] = (stop_bits_cnt[CRT]) ? RX_IDLE : RX_DONE; 
                                    fifo_if.write_i = (stop_bits_cnt[CRT] & !fifo_if.full_o);
                                    rx_done_o = stop_bits_cnt[CRT];
                                end
                            
                                default: begin 
                                    if (data_rx[CRT] == SYN) begin 
                                        syn_data_cnt[NXT] = syn_data_cnt[CRT] + 1'b1;
                                    end else begin 
                                        syn_data_cnt[NXT] = 'b0;
                                    end
                                    
                                    state[NXT] = RX_IDLE; 
                                    fifo_if.write_i = !fifo_if.full_o;
                                    rx_done_o = 1'b1;
                                end
                            endcase
                        end else begin 
                            counter_16br[NXT] = counter_16br[CRT] + 1'b1;
                        end
                    end
                end
            endcase
        end


        always_comb begin : fifo_write_data_assignment
            /* Depending on the data width configuration the data received could 
             * not be shifted out completley */
            case (data_width_i)
                DW_5BIT: fifo_if.wr_data_i[7:0] = {3'b0, data_rx[CRT][7:3]};
                DW_6BIT: fifo_if.wr_data_i[7:0] = {2'b0, data_rx[CRT][7:2]};
                DW_7BIT: fifo_if.wr_data_i[7:0] = {1'b0, data_rx[CRT][7:1]};
                DW_8BIT: fifo_if.wr_data_i[7:0] = data_rx[CRT][7:0];
            endcase
    
            case (parity_mode_i)
                EVEN:    fifo_if.wr_data_i[PARITY_BIT] = parity_bit[CRT] ^ 1'b0;
                ODD:     fifo_if.wr_data_i[PARITY_BIT] = parity_bit[CRT] ^ 1'b1;
                default: fifo_if.wr_data_i[PARITY_BIT] = 1'b0;
            endcase

            /* AND the stop bits with the RX line: if the first stop bits was 0
             * then 'stop_bits[CRT]' would be 0 too generating a frame error. 
             * The same goes for the single stop bit. If uart is receiving 0x00
             * then frame error is disabled */
            fifo_if.wr_data_i[FRAME] = !(stop_bits[CRT] & rx_i);

            /* Raise an overrun error if the fifo has reached the threshold level or
             * the data has been received and the device is receiving other data */
            fifo_if.wr_data_i[OVERRUN] = rx_rdy_int[CRT] & (state[CRT] != RX_IDLE);
        end : fifo_write_data_assignment

    /* Output assignment */
    assign data_rx_o = fifo_if.rd_data_o[7:0];
    assign rxd_rdy_o = rx_rdy_int[CRT];

    /* Should be asserted for only 1 clock cycle */
    assign frame_error_o = fifo_if.rd_data_o[FRAME] & rx_fifo_read_i;
    assign overrun_error_o = fifo_if.rd_data_o[OVERRUN] & rx_fifo_read_i;
    assign parity_o = fifo_if.rd_data_o[PARITY_BIT] & rx_fifo_read_i;

    /* If the threshold is set to 0 and DSM is active, the signal 'rxd_rdy_o' already signal the fifo being full. */
    assign rx_fifo_full_o = (rx_data_stream_mode_i & (threshold_i == 6'b0)) ? 1'b0 : fifo_if.full_o;


//--------------//
//  ASSERTIONS  //
//--------------//

    /* Reset FSM state with an acknowledge */
    property req_ackn_state_chk;
        @(posedge clk_i) ((counter_10ms[CRT] == COUNT_1MS) && req_ackn_i) |=> (state[CRT] == RX_IDLE);
    endproperty

    /* While not in data stream mode, the interrupt must be asserted while receiving the stop bits */
    property interrupt_raise_chk;
        @(posedge clk_i) (!rx_data_stream_mode_i && (state[CRT] == RX_DONE)) |=> rxd_rdy_o;
    endproperty

    /* The interrupt should be asserted till it's cleared with a read */
    property interrupt_clear_chk;
        @(posedge clk_i) $rose(rxd_rdy_o) && !rx_data_stream_mode_i |=> (rxd_rdy_o throughout rx_fifo_read_i [->1]) ##1 !rxd_rdy_o;
    endproperty

    /* Check frame error detection */
    property frame_error_chk;
        @(posedge clk_i) (!rx_i && (state[CRT] == RX_DONE)) |-> !fifo_if.wr_data_i[FRAME];
    endproperty

    /* Check threshold logic */
    property threshold_empty_chk;
        @(posedge clk_i) (fifo_size_cnt[CRT] == 0) |-> fifo_if.empty_o;
    endproperty

endmodule : receiver