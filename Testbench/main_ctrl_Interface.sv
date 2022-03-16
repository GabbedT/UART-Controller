`ifndef MAIN_CTRL_INTERFACE_SV
  `define MAIN_CTRL_INTERFACE_SV

import UART_PKG::*;

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
    /* FIFO operations */
    logic         rx_fifo_read_o;
    logic         tx_fifo_write_o;
    /* Data */
    logic [7:0]   data_tx_o;
    /* Error */
    uart_error_s  error_o;

//-----------------//
// CLOCKING BLOCKS //
//-----------------//


endinterface : main_ctrl_interface

`endif  