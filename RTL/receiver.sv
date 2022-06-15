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

`ifndef RECEIVER_INCLUDE
    `define RECEIVER_INCLUDE

`include "Packages/uart_pkg.sv"
`include "sync_FIFO_buffer.sv"

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
    output logic         parity_error_o,             
    output logic         rx_data_ready_o,             
    output logic [7:0]   data_rx_o,              
    output logic         rx_idle_o              
);

//--------------//
//  PARAMETERS  //
//--------------//

    /* Index in fifo data */
    localparam FRAME = 8;
    localparam OVERRUN = 9;
    localparam PARITY = 10;


//-----------//
//  RX FIFO  //
//-----------//

    logic        read_i;
    logic        fifo_rst_n_i;
    logic        fifo_write, fifo_read;
    logic        fifo_full, fifo_empty;
    logic [10:0] fifo_data_read, fifo_data_write;

    sync_FIFO_buffer #(11, RX_FIFO_DEPTH, 1) rx_fifo (
        .clk_i     ( clk_i           ),
        .rst_n_i   ( fifo_rst_n_i    ),
        .read_i    ( fifo_read       ),
        .write_i   ( fifo_write      ),
        .wr_data_i ( fifo_data_write ),
        .rd_data_o ( fifo_data_read  ),
        .full_o    ( fifo_full       ),
        .empty_o   ( fifo_empty      )
    );

    /* Reset fifo if a configuration request is received */
    logic fifo_rst_n;

    assign fifo_rst_n_i = rst_n_i & fifo_rst_n;
    assign fifo_read = rx_fifo_read_i;
    assign rx_fifo_empty_o = fifo_empty;


//------------//
//  DATAPATH  //
//------------//

    /* Data received */
    logic [7:0] data_rx_CRT, data_rx_NXT;

    /* Counter for data oversampling (16 times the baudrate) */
    logic [3:0] counter_16br_CRT, counter_16br_NXT;

    /* Number of data bits received */
    logic [2:0] bits_processed_CRT, bits_processed_NXT;

    /* Number of stop bits received */
    logic stop_bits_cnt_CRT, stop_bits_cnt_NXT;

    /* Store parity and stop bits of data received */
    logic parity_bit_CRT, parity_bit_NXT;
    logic stop_bits_CRT, stop_bits_NXT;

    /* Count the amount of consecuteve SYN character received */
    logic [$clog2(SYN_NUMBER) - 1:0] syn_data_cnt_CRT, syn_data_cnt_NXT;

        always_ff @(posedge clk_i or negedge rst_n_i) begin
            if (!rst_n_i) begin
                data_rx_CRT <= 8'b0;
                counter_16br_CRT <= 4'b0;
                bits_processed_CRT <= 3'b0;
                stop_bits_cnt_CRT <= 1'b0;
                parity_bit_CRT <= 1'b0;
                stop_bits_CRT <= 1'b1;
                syn_data_cnt_CRT <= 2'b0;
            end else begin 
                data_rx_CRT <= data_rx_NXT;
                counter_16br_CRT <= counter_16br_NXT;
                bits_processed_CRT <= bits_processed_NXT;
                stop_bits_cnt_CRT <= stop_bits_cnt_NXT;
                parity_bit_CRT <= parity_bit_NXT;
                stop_bits_CRT <= stop_bits_NXT;
                syn_data_cnt_CRT <= syn_data_cnt_NXT;
            end
        end 


    /* Counter to determine the amount of time the RX line 
     * stays low during configuration request */
    logic [$clog2(COUNT_1MS) - 1:0] counter_1ms_CRT, counter_1ms_NXT;

        always_ff @(posedge clk_i or negedge rst_n_i) begin : ms10_counter
            if (!rst_n_i) begin 
                counter_1ms_CRT <= 'b0;
            end else begin
                counter_1ms_CRT <= counter_1ms_NXT;
            end
        end : ms10_counter

        always_comb begin : ms10_counter_logic
            if (rx_i != RX_LINE_IDLE) begin 
                counter_1ms_NXT = counter_1ms_CRT + 1'b1;
            end else if (counter_1ms_CRT == COUNT_1MS) begin 
                counter_1ms_NXT = 'b0;
            end else begin 
                counter_1ms_NXT = 'b0;
            end
        end : ms10_counter_logic

  
    /* In data stream mode the device will interrupt if a certain
     * amount of data is received. The counter will go from 0 
     * (empty fifo) to FIFO_DEPTH - 1, if the programmer wants
     * the device to interrupt when fifo is full, then the threshold
     * must be set with the value 0. */
    logic [5:0] fifo_size_cnt_CRT, fifo_size_cnt_NXT;

        always_ff @(posedge clk_i or negedge rst_n_i) begin : fifo_size_counter
            if (!rst_n_i) begin 
                fifo_size_cnt_CRT <= 'b0;
            end else begin 
                fifo_size_cnt_CRT <= fifo_size_cnt_NXT;
            end 
        end : fifo_size_counter

        always_comb begin : fifo_size_counter_logic
            case ({fifo_write, fifo_read})
                /* Writing */
                2'b10: fifo_size_cnt_NXT = fifo_size_cnt_CRT + 1'b1;
                /* Reading */
                2'b01: fifo_size_cnt_NXT = fifo_size_cnt_CRT - 1'b1;
                /* Both or no operation */
                default: fifo_size_cnt_NXT = fifo_size_cnt_CRT;
            endcase
        end : fifo_size_counter_logic


    /* Configuration process requested. The request will be asserted
     * when the counter reaches the right value (RX low for 10ms) and
     * deasserted when the request is acknowledged */
    logic cfg_req_CRT, cfg_req_NXT;

        always_ff @(posedge clk_i or negedge rst_n_i) begin 
            if (!rst_n_i) begin 
                cfg_req_CRT <= 1'b0;
            end else if (req_ackn_i) begin 
                cfg_req_CRT <= 1'b0;
            end else begin 
                cfg_req_CRT <= cfg_req_NXT;
            end
        end

    assign config_req_slv_o = cfg_req_CRT;


//-------------//
//  FSM LOGIC  //
//-------------//

    /* FSM current and next state */
    receiver_fsm_e state_CRT, state_NXT;

        always_ff @(posedge clk_i or negedge rst_n_i) begin : fsm_state_register
            if (!rst_n_i) begin 
                state_CRT <= RX_IDLE;
            end else if (!fifo_rst_n) begin 
                state_CRT <= RX_IDLE;
            end else begin 
                state_CRT <= state_NXT;
            end
        end : fsm_state_register


    /* Data ready interrupt */
    logic data_ready;

        always_comb begin 

            //------------------//
            //  DEFAULT VALUES  //
            //------------------//

            state_NXT = state_CRT;
            data_rx_NXT = data_rx_CRT;
            stop_bits_NXT = stop_bits_CRT;
            parity_bit_NXT = parity_bit_CRT;
            counter_16br_NXT = counter_16br_CRT;
            syn_data_cnt_NXT = syn_data_cnt_CRT;
            stop_bits_cnt_NXT = stop_bits_cnt_CRT;
            bits_processed_NXT = bits_processed_CRT;
            cfg_req_NXT = cfg_req_CRT;  

            rx_idle_o = 1'b0;   
            fifo_write = 1'b0;  
            fifo_rst_n = 1'b1;  

            case (state_CRT)

                /* 
                 *  The device is waiting for data to arrives.
                 */
                RX_IDLE: begin 
                    stop_bits_cnt_NXT = 1'b0;
                    stop_bits_NXT = 1'b0;
                    rx_idle_o = 1'b1;

                    if ((rx_i != RX_LINE_IDLE) & enable) begin 
                        counter_16br_NXT = 4'b0;
                        state_NXT = (syn_data_cnt_CRT == SYN_NUMBER) ? RX_CONFIG_REQ : RX_START;
                    end
                end

                /* 
                 *  The device is receiving a configuration request. This state 
                 *  is reached after receiving 3 SYN character. 
                 */
                RX_CONFIG_REQ: begin
                    syn_data_cnt_NXT = 'b0;

                    /* Could be a false request, recover from it */
                    if (rx_i == RX_LINE_IDLE) begin 
                        state_NXT = RX_IDLE;
                    end else if (counter_1ms_CRT == COUNT_1MS) begin 
                        /* Go in IDLE then wait the request. The master won't initiate
                         * other transaction until the request is acknowledged */
                        cfg_req_NXT = 1'b1;
                        state_NXT = RX_IDLE;

                        /* Reset fifo only if the request is acknowledged */
                        fifo_rst_n = !req_ackn_i;
                    end
                end

                /* 
                 *  Sample the start bit in T/2 time (T is the bit while the
                 *  bit is stable) to grant maximum signal integrity.
                 */
                RX_START: begin 
                    if (ov_baud_rt_i) begin 
                        /* Reach the middle of the bit */
                        if (counter_16br_CRT == 4'd7) begin 
                            bits_processed_NXT = 3'b0;
                            counter_16br_NXT = 4'b0;
                            state_NXT = RX_SAMPLE;
                        end else begin 
                            counter_16br_NXT = counter_16br_CRT + 1'b1;
                        end
                    end
                end

                /* 
                 *  Sample data bits. Since in the START state the counter stopped
                 *  at half of the bit and then switched state, now every time the
                 *  counter reach T, it is in the middle of the data bit. The LSB
                 *  is received first.
                 */
                RX_SAMPLE: begin 
                    /* Reset stop bits */
                    stop_bits_NXT = 1'b1;

                    if (ov_baud_rt_i) begin 
                        if (counter_16br_CRT == 4'd15) begin 
                            counter_16br_NXT = 4'b0;
                            bits_processed_NXT = bits_processed_CRT + 1'b1;

                            /* Place the bit in the MSB of the data register,
                             * in the next clock cycle it will be shifted to 
                             * the right */
                            data_rx_NXT = {rx_i, data_rx_CRT[7:1]};

                            if (parity_mode_i[1]) begin
                                case (data_width_i) 
                                    DW_5BIT: state_NXT = (bits_processed_CRT == 4'd4) ? RX_DONE : RX_SAMPLE;
                                    DW_6BIT: state_NXT = (bits_processed_CRT == 4'd5) ? RX_DONE : RX_SAMPLE;
                                    DW_7BIT: state_NXT = (bits_processed_CRT == 4'd6) ? RX_DONE : RX_SAMPLE;
                                    DW_8BIT: state_NXT = (bits_processed_CRT == 4'd7) ? RX_DONE : RX_SAMPLE;
                                endcase
                            end else begin 
                                case (data_width_i) 
                                    DW_5BIT: state_NXT = (bits_processed_CRT == 4'd4) ? RX_PARITY : RX_SAMPLE;
                                    DW_6BIT: state_NXT = (bits_processed_CRT == 4'd5) ? RX_PARITY : RX_SAMPLE;
                                    DW_7BIT: state_NXT = (bits_processed_CRT == 4'd6) ? RX_PARITY : RX_SAMPLE;
                                    DW_8BIT: state_NXT = (bits_processed_CRT == 4'd7) ? RX_PARITY : RX_SAMPLE;
                                endcase
                            end
                        end else begin 
                            counter_16br_NXT = counter_16br_CRT + 1'b1;
                        end
                    end 
                end

                /* 
                 *  Sample parity bit. 
                 */
                RX_PARITY: begin 
                    if (ov_baud_rt_i) begin 
                        if (counter_16br_CRT == 4'd15) begin 
                            counter_16br_NXT = 4'b0;
                            parity_bit_NXT = rx_i;
                            state_NXT = RX_DONE;
                        end else begin 
                            counter_16br_NXT = counter_16br_CRT + 1'b1;
                        end
                    end 
                end

                /* 
                 *  During DONE state, the stop bits are detected. During 
                 *  this time the RX line must be stable on IDLE.
                 */
                RX_DONE: begin 
                    if (ov_baud_rt_i) begin
                        if (counter_16br_CRT == 4'd15) begin
                            /* AND the rx line with the stop bits so if in the
                             * previous cycle the stop bits wasn't detected 
                             * (logic 0) then the information doesn't get lost */
                            stop_bits_NXT = stop_bits_CRT & rx_i;

                            case (stop_bits_number_i)
                                SB_2BIT: begin 
                                    stop_bits_cnt_NXT = 1'b1;
                                    state_NXT = (stop_bits_cnt_CRT) ? RX_IDLE : RX_DONE; 
                                    fifo_write = (stop_bits_cnt_CRT & !fifo_full);
                                end
                            
                                default: begin 
                                    state_NXT = RX_IDLE; 
                                    fifo_write = !fifo_full;
                                end
                            endcase
                        end else begin 
                            counter_16br_NXT = counter_16br_CRT + 1'b1;
                        end
                    end

                    if (state_NXT == RX_IDLE) begin
                        if (data_rx_CRT == SYN) begin 
                            syn_data_cnt_NXT = syn_data_cnt_CRT + 1'b1;
                        end else begin
                            syn_data_cnt_NXT = 'b0;
                        end
                    end
                end
            endcase
        end


        always_comb begin : rx_done_interrupt_logic
            /* Raise an interrupt */
            if ((state_NXT == RX_IDLE) & (state_CRT == RX_DONE)) begin
                if (rx_data_stream_mode_i) begin
                    if (threshold_i != 'b0) begin 
                        /* Interrupt if fifo size is greater or equal the threshold value */
                        data_ready = (fifo_size_cnt_CRT >= threshold_i);
                    end else begin 
                        /* Interrupt only if fifo is full */
                        data_ready = fifo_full;    
                    end 
                end else begin 
                    data_ready = 1'b1;
                end
            end else begin
                data_ready = 1'b0;
            end
        end : rx_done_interrupt_logic


        always_comb begin : fifo_write_data_assignment
            /* Depending on the data width configuration the data received could 
             * not be shifted out completley */
            case (data_width_i)
                DW_5BIT: fifo_data_write[7:0] = {3'b0, data_rx_CRT[7:3]};
                DW_6BIT: fifo_data_write[7:0] = {2'b0, data_rx_CRT[7:2]};
                DW_7BIT: fifo_data_write[7:0] = {1'b0, data_rx_CRT[7:1]};
                DW_8BIT: fifo_data_write[7:0] = data_rx_CRT[7:0];
            endcase

            /* AND the stop bits with the RX line: if the first stop bits was 0
             * then 'stop_bits_CRT' would be 0 too generating a frame error. 
             * The same goes for the single stop bit.  */
            fifo_data_write[FRAME] = (state_CRT == RX_DONE) & !rx_i;

            /* Raise an overrun error if the fifo is full and new data is arriving */
            fifo_data_write[OVERRUN] = fifo_full & (state_CRT != RX_IDLE);
        end : fifo_write_data_assignment

    /* Output assignment */
    assign data_rx_o = (rx_fifo_read_i) ? fifo_data_read[7:0] : 8'b0;
    assign rx_data_ready_o = data_ready;

    /* If the threshold is set to 0 and DSM is active, the signal 'rx_data_ready_o' already signal the fifo being full. */
    assign rx_fifo_full_o = (rx_data_stream_mode_i & (threshold_i == 6'b0)) ? 1'b0 : fifo_full;

//-------------------------//
//  ERROR DETECTION LOGIC  //
//-------------------------//

    logic parity;

        always_comb begin : parity_detection_logic

            /*
             *  There are two types of parity checking: EVEN and ODD. Both are 
             *  computed by XORing every bit of the data, the difference 
             *  resides in the last bit XORed: 
             *  EVEN: parity ^ 0
             *  ODD:  parity ^ 1
             */
            
            case (data_width_i)
                DW_5BIT:  parity = ^data_rx_CRT[4:0];
                DW_6BIT:  parity = ^data_rx_CRT[5:0];
                DW_7BIT:  parity = ^data_rx_CRT[6:0];
                DW_8BIT:  parity = ^data_rx_CRT;
            endcase

            /* Select ODD or EVEN parity */
            case (parity_mode_i)
                EVEN:    fifo_data_write[PARITY] = parity_bit_CRT != (parity ^ 1'b0);
                ODD:     fifo_data_write[PARITY] = parity_bit_CRT != (parity ^ 1'b1);
                default: fifo_data_write[PARITY] = 1'b0;
            endcase
        end : parity_detection_logic

    /* Should be asserted for only 1 clock cycle */
    assign frame_error_o = fifo_data_read[FRAME] & rx_fifo_read_i;
    assign overrun_error_o = fifo_data_read[OVERRUN] & rx_fifo_read_i;
    assign parity_error_o = fifo_data_read[PARITY] & rx_fifo_read_i;

endmodule : receiver

`endif