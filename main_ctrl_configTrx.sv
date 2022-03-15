`ifndef MAIN_CTRL_CONFIG_TRX_SV
  `define MAIN_CTRL_CONFIG_TRX_SV

class main_ctrl_configTrx;
  
  logic         config_req_slv_i;
  logic         config_req_mst_i;
  logic         std_config_i;
  logic         data_stream_mode_i;
  logic         req_ackn_i;

  logic         STR_en_o;
  logic         config_req_mst_o;
  logic         data_stream_mode_o;
  logic         configuration_done_o;
  
  UART_pkg::uart_config_s config_o;

  /* Device configuration */
  static uart_config_s config_i;

//-------------//
// CONSTRUCTOR //
//-------------//

  function new();
    config_req_slv_i = 1'b0;
    config_req_mst_i = 1'b0;
    std_config_i = 1'b0;
    data_stream_mode_i = 1'b0;
    req_ackn_i = 1'b0;
    STR_en_o = 1'b0;
    config_o = config_i;
    config_req_mst_o = 1'b0;
    data_stream_mode_o = 1'b0;
    configuration_done_o = 1'b1;
  endfunction : new

//-----------//
// FUNCTIONS //
//-----------//

  /* Display configuration state of the device */
  function void displayConfig(string tag);
    $display("[%0s] [%0dns] DEVICE STATE:", tag, $time);
    $display("[%0s] [%0dns] DATA WIDTH = %0d", config_i.data_width);
    $display("[%0s] [%0dns] PARITY MODE = %0d", config_i.parity_mode);
    $display("[%0s] [%0dns] STOP BITS = %0d", config_i.stop_bits);
  endfunction : displayConfig

endclass : main_ctrl_configTrx

`endif