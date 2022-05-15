`ifndef UART_TX_DRIVER 
  `define UART_TX_DRIVER

`include "uart_trx.sv"
`include "uart_interface.sv"

import UART_pkg::*;
import registers_pkg::*;

class uart_tx_driver;

  /* Transmitter interface */
  tx_interface tx_if;

  mailbox tx2mon_mbx;

  event txDone_ev;


//---------------//
//  CONSTRUCTOR  //
//---------------//

  function new(input virtual tx_interface, input event txDone_ev, input mailbox tx2mon_mbx);
    this.tx_if = tx_if;
    this.tx2mon_mbx = tx2mon_mbx;
    this.txDone_ev = txDone_ev;
  endfunction : new 


//--------//
//  MAIN  //
//--------//

  /* 
   *  Basic task of transmitter module 
   */
  task main();
    forever begin 
      /* Write TX FIFO, then wait for the transmitter
       * to end its task */
      tx_if.tx_fifo_write_i <= !tx_if.tx_fifo_full_o;
      tx_if.data_tx_i <= $urandom();
      tx2mon_mbx.put(tx_if.data_tx_i);
      @(posedge tx_if.clk_i);
      tx_if.tx_fifo_write_i <= 1'b0;
      
      $display("[TX Driver][%0dns] Transmitter is sending data...", $time); 
      wait(tx_if.tx_done_o);
      $display("[TX Driver][%0dns] Transmission done!", $time); 
      ->txDone_ev;
    end
  endtask : tx_send_data



endclass : uart_tx_driver


`endif