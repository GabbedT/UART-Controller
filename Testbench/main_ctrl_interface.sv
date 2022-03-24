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
// FILE NAME : main_ctrl_interface.sv
// DEPARTMENT : 
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// ------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : UART main controller interface.
// ------------------------------------------------------------------------------------
// KEYWORDS : TASK
// ------------------------------------------------------------------------------------

`ifndef MAIN_CTRL_INTERFACE_SV
  `define MAIN_CTRL_INTERFACE_SV

import UART_pkg::*;

interface main_ctrl_interface (input logic clk_i);

  logic         rst_n_i;
  logic         interrupt_ackn_i;
  /* Data */
  data_packet_u data_rx_i;
  logic [7:0]   data_tx_i;
  /* Transmitter */
  logic         tx_done_i;
  logic         req_done_i;
  /* Error detection */
  logic         frame_error_i;
  logic         parity_i;
  logic         overrun_error_i;   
  logic         configuration_error_i;     
  /* FIFO status */ 
  logic         rx_fifo_empty_i;
  logic         tx_fifo_empty_i;
  logic         rx_fifo_read_i;
  logic         tx_fifo_write_i;
  /* Configuration */
  logic         config_req_slv_i;
  logic         config_req_mst_i;
  logic         std_config_i;
  uart_config_s config_i;
  logic         data_stream_mode_i;
  logic         req_ackn_i;

  logic         STR_en_o;
  uart_config_s config_o;
  logic         config_req_mst_o;
  logic         data_stream_mode_o;
  logic         configuration_done_o;
  logic         req_ackn_o;
  /* FIFO operations */
  logic         rx_fifo_read_o;
  logic         tx_fifo_write_o;
  /* Data */
  logic [7:0]   data_tx_o;
  /* Error */
  uart_error_s  error_o;


//--------//
//  TASK  //
//--------//

  task reset();
    interrupt_ackn_i <= 1'b0;
    data_rx_i <= 'b0;
    data_tx_i <= 'b0;
    tx_done_i <= 1'b0;
    req_done_i <= 1'b0;
    frame_error_i <= 1'b0;
    parity_i <= 1'b1;
    overrun_error_i <= 1'b0;
    configuration_error_i <= 1'b0;
    rx_fifo_empty_i <= 1'b1;
    tx_fifo_empty_i <= 1'b1;
    rx_fifo_read_i <= 1'b0; 
    tx_fifo_write_i <= 1'b0;
    config_req_slv_i <= 1'b0;
    config_req_mst_i <= 1'b0;
    std_config_i <= 1'b0;
    config_i <= STD_CONFIGURATION;
    data_stream_mode_i <= 1'b0;
    req_ackn_i <= 1'b0;
  endtask : reset 

endinterface : main_ctrl_Interface

`endif  
