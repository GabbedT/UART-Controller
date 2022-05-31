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


import UART_pkg::*;

module transmitter (
    input  logic         clk_i,
    input  logic         rst_n_i,
    input  logic         enable,
    input  logic         ov_baud_rt_i,
    input  logic [7:0]   data_tx_i,
    input  logic         tx_fifo_write_i,
    input  logic         config_req_mst_i,
    input  logic         config_req_slv_i,
    input  logic         tx_data_stream_mode_i,
    input  logic [1:0]   data_width_i,
    input  logic [1:0]   stop_bits_number_i,
    input  logic [1:0]   parity_mode_i,

    output logic         tx_o,
    output logic         tx_done_o,      
    output logic         req_done_o,
    output logic         tx_fifo_empty_o,
    output logic         tx_fifo_full_o,
    output logic         tx_idle_o
);

//-----------//
//  TX FIFO  //
//-----------//

    /* Interface declaration */
    sync_fifo_interface #(8) fifo_if(clk_i);

    assign fifo_if.wr_data_i = data_tx_i;
    assign fifo_if.write_i = tx_fifo_write_i;
    assign fifo_if.rst_n_i = rst_n_i | config_req_slv_i; 

    /* FIFO buffer instantiation in FWFT mode */
    sync_FIFO_buffer #(TX_FIFO_DEPTH, 1) tx_fifo (clk_i, fifo_if);

    assign tx_fifo_full_o = fifo_if.full_o;
    assign tx_fifo_empty_o = fifo_if.empty_o;


//------------//
//  DATAPATH  //
//------------//

    /* Data to be transmitted */
    logic [7:0] data_tx[NXT:CRT];

    /* Counter to determine the amount of time the TX line 
     * must stay low during configuration request */
    logic [$clog2(COUNT_1MS) - 1:0] counter_10ms[NXT:CRT];

    /* Drive the TX line */
    logic tx_line;

    /* Counter for baudrate */
    logic [3:0] counter_br[NXT:CRT];

    /* Number of stop bits sended */
    logic stop_bits[NXT:CRT];

    /* Number of data bits sended */
    logic [2:0] bits_processed[NXT:CRT]; 

        /* Register the output to not lose data */
        always_ff @(posedge clk_i) begin : data_register
            if (!rst_n_i) begin
                data_tx[CRT] <= 8'b0;
                counter_10ms[CRT] <= 'b0;
                counter_br[CRT] <= 4'b0;
                bits_processed[CRT] <= 3'b0;
                stop_bits[CRT] <= 1'b0;
                tx_o <= TX_LINE_IDLE;
            end else begin 
                data_tx[CRT] <= data_tx[NXT];
                counter_10ms[CRT] <= counter_10ms[NXT];
                counter_br[CRT] <= counter_br[NXT];
                bits_processed[CRT] <= bits_processed[NXT];
                stop_bits[CRT] <= stop_bits[NXT];
                tx_o <= tx_line;
            end
        end : data_register


//-------------//
//  FSM LOGIC  //
//-------------//

    /* FSM current and next state */
    fsm_pkg::transmitter_fsm_e state[NXT:CRT];

        always_ff @(posedge clk_i) begin : fsm_state_register
            if (!rst_n_i) begin 
                state[CRT] <= TX_IDLE;
            end else if (config_req_slv_i) begin 
                state[CRT] <= TX_IDLE;
            end else begin 
                state[CRT] <= state[NXT];
            end
        end : fsm_state_register


        always_comb begin : fsm_next_state_logic

            //------------------//
            //  DEFAULT VALUES  //
            //------------------//

            state[NXT] = state[CRT];
            data_tx[NXT] = data_tx[CRT];
            stop_bits[NXT] = stop_bits[CRT];
            counter_br[NXT] = counter_br[CRT];
            counter_10ms[NXT] = counter_10ms[CRT];
            bits_processed[NXT] = bits_processed[CRT];

            tx_line = TX_LINE_IDLE;
            tx_done_o = 1'b0;
            tx_idle_o = 1'b0;
            fifo_if.read_i = 1'b0;
            req_done_o = 1'b0;

            case (state[CRT])

                /* 
                 *  The device is simply waiting for data to transmit. If there 
                 *  is a configuration request and FIFO is not empty, clear the 
                 *  buffer by transmitting all the data, then send the request.
                 */
                TX_IDLE: begin 
                    stop_bits[NXT] = 1'b0;
                    tx_idle_o = 1'b1;

                    if (!fifo_if.empty_o & enable) begin 
                        state[NXT] = TX_START;
                    end else if (config_req_mst_i) begin 
                        state[NXT] = TX_CFG_REQ;
                    end
                end

                /* 
                 *  Set tx line to logic 0 for 10ms.  
                 */
                TX_CFG_REQ: begin 
                    counter_10ms[NXT] = counter_10ms[CRT] + 1'b1;
                    tx_line = !TX_LINE_IDLE;

                    if (counter_10ms[CRT] == COUNT_1MS) begin 
                        req_done_o = 1'b1;
                        state[NXT] = TX_IDLE;
                        counter_10ms[NXT] = 'b0;
                    end
                end

                /* 
                 *  Send start bit the the receiver device and load the data
                 *  register with the data to be transmitted.
                 */
                TX_START: begin 
                    tx_line = !TX_LINE_IDLE;

                    if (ov_baud_rt_i) begin 
                        if (counter_br[CRT] == 4'd15) begin 
                            state[NXT] = TX_DATA;
                            counter_br[NXT] = 4'b0;
                            fifo_if.read_i = 1'b1;
                            data_tx[NXT] = fifo_if.rd_data_o;                
                        end else begin 
                            counter_br[NXT] = counter_br[CRT] + 1'b1;
                        end
                    end
                end

                /* 
                 *  Send data bits serially, every 16 tick process the next bit of data.
                 */
                TX_DATA: begin 
                    tx_line = data_tx[CRT][0];

                    if (ov_baud_rt_i) begin 
                        if (counter_br[CRT] == 4'd15) begin 
                            /* Shift the data to send the next bit and increment
                             * the bit counter */
                            data_tx[NXT] = data_tx[CRT] >> 1'b1;
                            bits_processed[NXT] = bits_processed[CRT] + 1'b1;
                            counter_br[NXT] = 4'b0;

                            /* Send a fixed amount of bits based on configuration parameter */
                            if (parity_mode_i[1]) begin
                                case (data_width_i)  
                                    DW_5BIT:  state[NXT] = (bits_processed[CRT] == 4'd4) ? TX_DONE : TX_DATA;
                                    DW_6BIT:  state[NXT] = (bits_processed[CRT] == 4'd5) ? TX_DONE : TX_DATA;
                                    DW_7BIT:  state[NXT] = (bits_processed[CRT] == 4'd6) ? TX_DONE : TX_DATA;
                                    DW_8BIT:  state[NXT] = (bits_processed[CRT] == 4'd7) ? TX_DONE : TX_DATA;
                                endcase
                            end else begin 
                                case (data_width_i)  
                                    DW_5BIT:  state[NXT] = (bits_processed[CRT] == 4'd4) ? TX_PARITY : TX_DATA;
                                    DW_6BIT:  state[NXT] = (bits_processed[CRT] == 4'd5) ? TX_PARITY : TX_DATA;
                                    DW_7BIT:  state[NXT] = (bits_processed[CRT] == 4'd6) ? TX_PARITY : TX_DATA;
                                    DW_8BIT:  state[NXT] = (bits_processed[CRT] == 4'd7) ? TX_PARITY : TX_DATA;
                                endcase
                            end
                        end else begin 
                            counter_br[NXT] = counter_br[CRT] + 1'b1;
                        end
                    end
                end

                /* 
                 *  Send parity bit.
                 */
                TX_PARITY: begin 
                    case (parity_mode_i[0])
                        /* EVEN */
                        0: tx_line = (^data_tx[CRT]) ^ 1'b0;
                        /* ODD */
                        1: tx_line = (^data_tx[CRT]) ^ 1'b1;
                    endcase

                    if (ov_baud_rt_i) begin
                        if (counter_br[CRT] == 4'd15) begin 
                            counter_br[NXT] = 4'b0;
                            state[NXT] = TX_DONE;
                        end else begin 
                            counter_br[NXT] = counter_br[CRT] + 1'b1;
                        end
                    end
                end

                /* 
                *  Send stop bits to end the transaction.
                */
                TX_DONE: begin 
                    tx_line = TX_LINE_IDLE;
                    bits_processed[NXT] = 3'b0;

                    if (ov_baud_rt_i) begin 
                        if (counter_br[CRT] == 4'd15) begin 
                            case (stop_bits_number_i)
                                SB_1BIT: begin 
                                    state[NXT] = TX_IDLE;
                                    tx_done_o = (tx_data_stream_mode_i) ? fifo_if.empty_o : 1'b1;
                                end

                                SB_2BIT: begin 
                                    state[NXT] = (stop_bits[CRT]) ? TX_IDLE : TX_DONE;
                                    tx_done_o = (tx_data_stream_mode_i) ? (fifo_if.empty_o & stop_bits[CRT]) : stop_bits[CRT];
                                    stop_bits[NXT] = 1'b1;
                                end

                                default: begin 
                                    state[NXT] = TX_IDLE;
                                    tx_done_o = (tx_data_stream_mode_i) ? fifo_if.empty_o : 1'b1;
                                end
                            endcase

                            counter_br[NXT] = 4'b0;
                        end else begin 
                            counter_br[NXT] = counter_br[CRT] + 1'b1;
                        end
                    end
                end

            endcase

      end : fsm_next_state_logic


//--------------//
//  ASSERTIONS  //
//--------------//

    /* After the device is done transmitting, lower the request signal */
    property req_done_chk;
    @(posedge clk_i) req_done_o |=> !config_req_mst_i;
    endproperty

    /* While sending the request, the tx line must be stable for 10ms */
    property tx_stable_chk;
    @(posedge clk_i) ((fifo_if.empty_o) && (state[CRT] == TX_CFG_REQ)) |-> (!tx_o[*COUNT_1MS]);
    endproperty

    /* Send two stop bits. Tx should be high for 2 clock cycles */
    property two_stop_bits_chk;
    @(posedge clk_i) ((state[CRT] == TX_DONE) && (stop_bits_number_i == SB_2BIT)) |=> (tx_o[*2]); 
    endproperty

    /* The FIFO must not be written if it's full */
    property full_chk;
    @(posedge clk_i) fifo_if.full_o |-> !tx_fifo_write_i;
    endproperty

    /* Read FIFO only in start state */
    property read_chk;
    @(posedge clk_i) (state[CRT] != TX_START) |-> !fifo_if.read_i;
    endproperty

    initial begin 
    
        assert property (req_done_chk)
        else $display("Request done, the request signal wasn't deassert!");

        assert property (tx_stable_chk)
        else $display("Tx line not stable on low");

        assert property (two_stop_bits_chk)
        else $display("Error on sending 2 stop bits, tx line must be stable on high for 2 clock cycles");

        assert property (full_chk)
        else $display("Writing on full FIFO, data lost!");

        assert property (read_chk)
        else $display("Reading fifo while not sending start bits, data lost!");

    end

endmodule : transmitter