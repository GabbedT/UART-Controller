`ifndef MAIN_CTRL_TRANSACTION_SV
  `define MAIN_CTRL_TRANSACTION_SV

import UART_pkg::*;

class main_ctrl_Transaction;

  logic         interrupt_ackn_i;
  uart_error_s  error_o;
  logic         configuration_error_i;
  logic         tx_done_i;
  logic         req_done_i;

  main_ctrl_dataTrx   dataTrx;
  main_ctrl_configTrx configTrx;

//------//
// DATA //
//------//

  /* Total number of transactions */
  static int trx_count = 1;

  /* Id of transaction */
  int trx_id;

  /* Time of creation to track faulty transactions */
  time trx_time;

//-------------//
// CONSTRUCTOR //
//-------------//

  function new(input bit increment = 0);
    interrupt_ackn_i = 1'b0;
    error_o = 'b0;
    configuration_error_i = 1'b0;
    tx_done_i = 1'b0;
    req_done_i = 1'b0;

    dataTrx = new();
    configTrx = new();

    trx_time = $time;
    if (increment) begin
      // Increment the number of transaction created every time
      // the testbench instantiate an object and assign the transaction
      // an unique id
      trx_id = trx_count++;
    end
  endfunction : new 

endclass : main_ctrl_Transaction

`endif 