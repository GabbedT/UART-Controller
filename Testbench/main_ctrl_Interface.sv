`ifndef MAIN_CTRL_INTERFACE_SV
  `define MAIN_CTRL_INTERFACE_SV

import UART_pkg::*;

interface main_ctrl_Interface (input logic clk_i);

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
  logic         req_ackn_i;
  /* FIFO operations */
  logic         rx_fifo_read_o;
  logic         tx_fifo_write_o;
  /* Data */
  logic [7:0]   data_tx_o;
  /* Error */
  uart_error_s  error_o;


//-------------------//
//  CLOCKING BLOCKS  //
//-------------------//

  clocking drv_cb @(posedge clk_i);
    default input #1ns output #1ns;
    output data_rx_i;
    output data_tx_i;
    output tx_done_i;
    output req_done_i;
    output frame_error_i;
    output parity_i;
    output overrun_error_i;   
    output configuration_error_i;
    output rx_fifo_empty_i;
    output tx_fifo_empty_i;
    output rx_fifo_read_i;
    output tx_fifo_write_i;
    output config_req_slv_i;
    output config_req_mst_i;
    output std_config_i;
    output config_i;
    output data_stream_mode_i;
    output req_ackn_i;

    input  STR_en_o;
    input  config_o;
    input  config_req_mst_o;
    input  data_stream_mode_o;
    input  configuration_done_o;
    input  req_ackn_i;
    input  rx_fifo_read_o;
    input  tx_fifo_write_o;
    input  data_tx_o;
    input  error_o;
  endclocking : driver_cb


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
    parity_i <= trxPacket.data.calc_parity(STD_PARITY_MODE, 'b0);
    overrun_error_i <= 1'b0;
    configuration_error_i <= 1'b0;
    rx_fifo_empty_i <= 1'b1;
    tx_fifo_empty_i <= 1'b1;
    rx_fifo_read_i <= 1'b0; 
    tx_fifo_write_i <= 1'b0;
    config_req_slv_i <= 1'b0;
    config_req_mst_i <= 1'b0;
    std_config_i <= 1'b0;
    config_i <= STD_CONFIG;
    data_stream_mode_i <= 1'b0;
    req_ackn_i <= 1'b0;
  endtask : reset 

endinterface : main_ctrl_Interface

`endif  