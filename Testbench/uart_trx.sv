`ifndef UART_TRX
  `define UART_TRX

import registers_pkg::*;

class uart_trx;

//--------//
//  DATA  //
//--------//

  /* DUT data */
  bit [7:0] data_io;
  bit [2:0] address_i;
  bit chip_sel_n_i;
  bit read_write_i;
  bit rx_i;
  bit tx_o;
  bit ireq_n_o;

  /* Testbench data */

  rand operation_t operation;

  /* UART configuration state */
  static bit [1:0] data_width;
  static bit [1:0] parity_mode;
  static bit [1:0] stop_bits;

  /* How many times an operation has beenn executed */
  static int coverage[9];


  /* Set operation frequency */
  constraint operation_frequency_c { operation dist { 
      READ_DATA          := 40,
      SEND_DATA          := 20,
      SEND_DATA_BURST    := 20,
      SET_THRESHOLD      := 3,
      SET_COM_MODE       := 3,
      ENABLE_CONFIG_REQ  := 3,
      ENABLE_INTERRUPT   := 3,
      NO_OPERATION       := 30
  };}

  /* Don't set disabled communication */
  constraint communication_mode_c { ((address_i == CTR_ADDR) & write_i) -> data_io[5:0] != 2'b00 ; }
  
endclass : uart_trx

`endif