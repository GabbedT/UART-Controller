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
// FILE NAME : transmitter.sv
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// ------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : This module contains the transmitter of the uart. It is composed by
//               a main FSM and a FIFO buffer. The FSM takes care of the transaction
//               timing and it can also initiate a configuration request (only if the 
//               buffer is empty). The fifo will just hold the data so the device can 
//               receive data to transmit while sending other transactions.
//               The transmitter takes as input an oversampling baud rate clock that 
//               has 16 times the frequency of the baud rate clock. 
// ------------------------------------------------------------------------------------
// KEYWORDS : PARAMETERS, TX FIFO, DATAPATH, FSM LOGIC, ASSERTIONS
// ------------------------------------------------------------------------------------

`ifndef TRANSMITTER_INCLUDE
    `define TRANSMITTER_INCLUDE

`include "Packages/uart_pkg.sv"
`include "sync_FIFO_buffer.sv"

module transmitter (
    input  logic         clk_i,
    input  logic         rst_n_i,
    input  logic         enable,                // From REGISTERS
    input  logic         ov_baud_rt_i,          // From BAUD RATE
    input  logic [7:0]   data_tx_i,             // From CU
    input  logic         tx_fifo_write_i,       // From CU
    input  logic         config_req_mst_i,      // From REGISTERS
    input  logic         config_req_slv_i,      // From RECEIVER
    input  logic         tx_data_stream_mode_i, // From REGISTERS
    input  logic [1:0]   data_width_i,          // From REGISTERS
    input  logic [1:0]   stop_bits_number_i,    // From REGISTERS
    input  logic [1:0]   parity_mode_i,         // From REGISTERS

    output logic         tx_o,          // To TOP
    output logic         tx_done_o,     // To REGISTERS and CONTROL UNIT
    output logic         req_done_o,    // To CONTROL UNIT
    output logic         tx_fifo_full_o, // To REGISTERS
    output logic         tx_idle_o      // To REGISTERS
);

//-----------//
//  TX FIFO  //
//-----------//

    logic       read_i;
    logic       fifo_rst_n_i;
    logic       fifo_full, fifo_empty;
    logic [7:0] fifo_data_read;

    sync_FIFO_buffer #(8, TX_FIFO_DEPTH, 1) tx_fifo (
        .clk_i     ( clk_i           ),
        .rst_n_i   ( fifo_rst_n_i    ),
        .read_i    ( read_i          ),
        .write_i   ( tx_fifo_write_i ),
        .wr_data_i ( data_tx_i       ),
        .rd_data_o ( fifo_data_read  ),
        .full_o    ( fifo_full       ),
        .empty_o   ( fifo_empty      )
    );

    assign fifo_rst_n_i = rst_n_i | config_req_slv_i;
    assign tx_fifo_full_o = fifo_full;


//------------//
//  DATAPATH  //
//------------//

    /* Data to be transmitted */
    logic [7:0] data_tx_CRT, data_tx_NXT;

    /* Counter to determine the amount of time the TX line 
     * must stay low during configuration request */
    logic [$clog2(COUNT_1MS) - 1:0] counter_10ms_CRT, counter_10ms_NXT;

    /* Drive the TX line */
    logic tx_line;

    /* Counter for baudrate */
    logic [3:0] counter_br_CRT, counter_br_NXT;

    /* Number of stop bits sended */
    logic stop_bits_CRT, stop_bits_NXT;

    /* Number of data bits sended */
    logic [2:0] bits_processed_CRT, bits_processed_NXT; 

        /* Register the output to not lose data */
        always_ff @(posedge clk_i or negedge rst_n_i) begin : data_register
            if (!rst_n_i) begin
                data_tx_CRT <= 8'b0;
                counter_10ms_CRT <= 'b0;
                counter_br_CRT <= 4'b0;
                bits_processed_CRT <= 3'b0;
                stop_bits_CRT <= 1'b0;
                tx_o <= TX_LINE_IDLE;
            end else begin 
                data_tx_CRT <= data_tx_NXT;
                counter_10ms_CRT <= counter_10ms_NXT;
                counter_br_CRT <= counter_br_NXT;
                bits_processed_CRT <= bits_processed_NXT;
                stop_bits_CRT <= stop_bits_NXT;
                tx_o <= tx_line;
            end
        end : data_register


//-------------//
//  FSM LOGIC  //
//-------------//

    /* FSM current and next state */
    transmitter_fsm_e state_CRT, state_NXT;

        always_ff @(posedge clk_i or negedge rst_n_i) begin : fsm_state_register
            if (!rst_n_i) begin 
                state_CRT <= TX_IDLE;
            end else if (config_req_slv_i) begin 
                state_CRT <= TX_IDLE;
            end else begin 
                state_CRT <= state_NXT;
            end
        end : fsm_state_register


        always_comb begin : fsm_next_state_logic

            //------------------//
            //  DEFAULT VALUES  //
            //------------------//

            state_NXT = state_CRT;
            data_tx_NXT = data_tx_CRT;
            stop_bits_NXT = stop_bits_CRT;
            counter_br_NXT = counter_br_CRT;
            counter_10ms_NXT = counter_10ms_CRT;
            bits_processed_NXT = bits_processed_CRT;

            tx_line = TX_LINE_IDLE;
            tx_done_o = 1'b0;
            tx_idle_o = 1'b0;
            read_i = 1'b0;
            req_done_o = 1'b0;

            case (state_CRT)

                /* 
                 *  The device is simply waiting for data to transmit. If there 
                 *  is a configuration request and FIFO is not empty, clear the 
                 *  buffer by transmitting all the data, then send the request.
                 */
                TX_IDLE: begin 
                    stop_bits_NXT = 1'b0;
                    tx_idle_o = 1'b1;

                    if (!fifo_empty & enable) begin 
                        state_NXT = TX_START;
                    end else if (config_req_mst_i & fifo_empty) begin 
                        state_NXT = TX_CFG_REQ;
                    end
                end

                /* 
                 *  Set tx line to logic 0 for 10ms.  
                 */
                TX_CFG_REQ: begin 
                    counter_10ms_NXT = counter_10ms_CRT + 1'b1;
                    tx_line = !TX_LINE_IDLE;

                    if (counter_10ms_CRT == COUNT_1MS) begin 
                        req_done_o = 1'b1;
                        state_NXT = TX_IDLE;
                        counter_10ms_NXT = 'b0;
                    end
                end

                /* 
                 *  Send start bit the the receiver device and load the data
                 *  register with the data to be transmitted.
                 */
                TX_START: begin 
                    tx_line = !TX_LINE_IDLE;

                    if (ov_baud_rt_i) begin 
                        if (counter_br_CRT == 4'd15) begin 
                            state_NXT = TX_DATA;
                            counter_br_NXT = 4'b0;
                            read_i = 1'b1;
                            data_tx_NXT = fifo_data_read;                
                        end else begin 
                            counter_br_NXT = counter_br_CRT + 1'b1;
                        end
                    end
                end

                /* 
                 *  Send data bits serially, every 16 tick process the next bit of data.
                 */
                TX_DATA: begin 
                    tx_line = data_tx_CRT[0];

                    if (ov_baud_rt_i) begin 
                        if (counter_br_CRT == 4'd15) begin 
                            /* Shift the data to send the next bit and increment
                             * the bit counter */
                            data_tx_NXT = data_tx_CRT >> 1'b1;
                            bits_processed_NXT = bits_processed_CRT + 1'b1;
                            counter_br_NXT = 4'b0;

                            /* Send a fixed amount of bits based on configuration parameter */
                            if (parity_mode_i[1]) begin
                                case (data_width_i)  
                                    DW_5BIT:  state_NXT = (bits_processed_CRT == 4'd4) ? TX_DONE : TX_DATA;
                                    DW_6BIT:  state_NXT = (bits_processed_CRT == 4'd5) ? TX_DONE : TX_DATA;
                                    DW_7BIT:  state_NXT = (bits_processed_CRT == 4'd6) ? TX_DONE : TX_DATA;
                                    DW_8BIT:  state_NXT = (bits_processed_CRT == 4'd7) ? TX_DONE : TX_DATA;
                                endcase
                            end else begin 
                                case (data_width_i)  
                                    DW_5BIT:  state_NXT = (bits_processed_CRT == 4'd4) ? TX_PARITY : TX_DATA;
                                    DW_6BIT:  state_NXT = (bits_processed_CRT == 4'd5) ? TX_PARITY : TX_DATA;
                                    DW_7BIT:  state_NXT = (bits_processed_CRT == 4'd6) ? TX_PARITY : TX_DATA;
                                    DW_8BIT:  state_NXT = (bits_processed_CRT == 4'd7) ? TX_PARITY : TX_DATA;
                                endcase
                            end
                        end else begin 
                            counter_br_NXT = counter_br_CRT + 1'b1;
                        end
                    end
                end

                /* 
                 *  Send parity bit.
                 */
                TX_PARITY: begin 
                    case (parity_mode_i[0])
                        /* EVEN */
                        0: tx_line = (^data_tx_CRT) ^ 1'b0;
                        /* ODD */
                        1: tx_line = (^data_tx_CRT) ^ 1'b1;
                    endcase

                    if (ov_baud_rt_i) begin
                        if (counter_br_CRT == 4'd15) begin 
                            counter_br_NXT = 4'b0;
                            state_NXT = TX_DONE;
                        end else begin 
                            counter_br_NXT = counter_br_CRT + 1'b1;
                        end
                    end
                end

                /* 
                *  Send stop bits to end the transaction.
                */
                TX_DONE: begin 
                    tx_line = TX_LINE_IDLE;
                    bits_processed_NXT = 3'b0;

                    if (ov_baud_rt_i) begin 
                        if (counter_br_CRT == 4'd15) begin 
                            case (stop_bits_number_i)
                                SB_1BIT: begin 
                                    state_NXT = TX_IDLE;
                                    tx_done_o = (tx_data_stream_mode_i) ? fifo_empty : 1'b1;
                                end

                                SB_2BIT: begin 
                                    state_NXT = (stop_bits_CRT) ? TX_IDLE : TX_DONE;
                                    tx_done_o = (tx_data_stream_mode_i) ? (fifo_empty & stop_bits_CRT) : stop_bits_CRT;
                                    stop_bits_NXT = 1'b1;
                                end

                                default: begin 
                                    state_NXT = TX_IDLE;
                                    tx_done_o = (tx_data_stream_mode_i) ? fifo_empty : 1'b1;
                                end
                            endcase

                            counter_br_NXT = 4'b0;
                        end else begin 
                            counter_br_NXT = counter_br_CRT + 1'b1;
                        end
                    end
                end

            endcase

      end : fsm_next_state_logic

endmodule : transmitter

`endif