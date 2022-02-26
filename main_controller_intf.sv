`ifndef MAIN_CONTROLLER_INTERFACE
  `define MAIN_CONTROLLER_INTERFACE
  
import UART_pkg::*;

interface main_controller_intf (input logic clk_i);

  // Inputs
  logic         rst_n_i;
  data_packet_u data_rx_i;
  logic [7:0]   data_tx_i;
  logic         frame_error_i;
  logic         config_en_i;
  uart_config_s config_i;
  logic         device_type_i;
  logic         parity_i;
  logic         rx_fifo_full_i;
  logic         tx_fifo_empty_i;
  logic         rx_fifo_read_i;
  logic         tx_fifo_write_i;
  logic         rx_i;
  logic         is_receiving_i;
  logic         baud_rt_tick_i;
  logic         autoconfig_en_i;

  // Outputs
  logic         tx_o;
  logic         drive_tx_o;
  logic         rx_fifo_read_o;
  logic         rx_fifo_write_o;
  logic         tx_fifo_read_o;
  logic         tx_fifo_write_o;
  logic [7:0]   data_tx_o;
  logic         config_en_o;
  uart_config_s config_o;
  uart_error_s  error_o;

endinterface 

`endif