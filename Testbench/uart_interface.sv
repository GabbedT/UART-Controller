`ifndef UART_INTERFACE
  `define UART_INTERFACE

import UART_pkg::*;

//-----------------//
//  DUT INTERFACE  //
//-----------------//

interface uart_interface (input logic clk_i, input logic rst_n_i);

  logic       chip_sel_n_i;
  logic [2:0] address_i;
  logic       read_write_i;
  logic [7:0] data_io;
  logic       rx_i;

  logic       tx_o;
  logic       ireq_n_o;


  task reset();
    chip_sel_n_i <= 1'b1;
    address_i <= 3'b0;
    read_write_i <= READ;
    rx_i <= 1'b1;
  endtask : reset

  task enable_chip();
    chip_sel_n_i <= 1'b0;
  endtask : enable_chip

  task disable_chip();
    chip_sel_n_i <= 1'b1;
  endtask : enable_chip

endinterface : uart_interface


//-------------------------//
//  TRANSMITTER INTERFACE  //
//-------------------------//

interface tx_interface (input logic clk_i, input logic rst_n_i);

  logic       enable;
  logic       ov_baud_rt_i;
  logic [7:0] data_tx_i;
  logic       tx_fifo_write_i;
  logic       config_req_mst_i;
  logic       tx_data_stream_mode_i;
  logic [1:0] data_width_i;
  logic [1:0] stop_bits_number_i;
  logic [1:0] parity_mode_i;

  logic       tx_o;
  logic       tx_done_o;     
  logic       req_done_o;
  logic       tx_fifo_empty_o;
  logic       tx_fifo_full_o;


  task reset();
    enable <= 1'b1;
    data_tx_i <= 8'b0;
    tx_fifo_write_i <= 1'b0;
    config_req_mst_i <= 1'b0;
    tx_data_stream_mode_i <= 1'b0;
    data_width_i <= STD_DATA_WIDTH;
    stop_bits_number_i <= STD_STOP_BITS;
    parity_mode_i <= STD_PARITY_MODE;
  endtask : reset 

endinterface : tx_interface


//----------------------//
//  RECEIVER INTERFACE  //
//----------------------//

interface rx_interface (input logic clk_i, input logic rst_n_i);

  logic         enable;
  logic         ov_baud_rt_i;
  logic         rx_i;
  logic         rx_fifo_read_i;
  logic         req_ackn_i;
  logic [5:0]   threshold_i;
  logic         rx_data_stream_mode_i;
  logic [1:0]   data_width_i;
  logic [1:0]   stop_bits_number_i;
  logic [1:0]   parity_mode_i;
 
  logic         rx_fifo_full_o;
  logic         rx_fifo_empty_o;
  logic         config_req_slv_o;
  logic         overrun_error_o;
  logic         frame_error_o;
  logic         parity_o;
  logic         rx_done_o;
  logic         rxd_rdy_o;
  logic [7:0]   data_rx_o;

  task reset();
    enable <= 1'b1; 
    rx_i <= 1'b1;
    rx_fifo_read_i <= 1'b0;
    req_ackn_i <= 1'b0;
    threshold_i <= 6'b0;
    rx_data_stream_mode_i <= 1'b0;
    data_width_i <= STD_DATA_WIDTH;
    stop_bits_number_i <= STD_STOP_BITS;
    parity_mode_i <= STD_PARITY_MODE;
  endtask : reset 

endinterface : rx_interface

`endif