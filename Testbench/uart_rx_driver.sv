`ifndef UART_RX_DRIVER 
  `define UART_RX_DRIVER

`include "uart_trx.sv"
`include "uart_interface.sv"

import UART_pkg::*;
import registers_pkg::*;

class uart_rx_driver;

  /* Receiver interface */
  rx_interface rx_if;

  bit [7:0] rx_data;

  mailbox rx2mon_mbx;
  event rxDone_ev;


//---------------//
//  CONSTRUCTOR  //
//---------------//

  function new(input virtual rx_interface rx_if, input mailbox rx2mon_mbx, input event rxDone_ev);
    this.rx_if = rx_if;
    this.rx2mon_mbx = rx2mon_mbx;
    this.rxDone_ev = rxDone_ev;
  endfunction : new


//---------//
//  TASKS  //
//---------//

  /* 
   *  Read data received 
   */  
  task rx_read_data();
    rx_if.read_i <= 1'b1;
    rx_data = rx_if.data_rx_o;

    /* Receive data and send to the monitor */
    rx2mon_mbx.put(rx_data);
    @(posedge rx_if.clk_i);
    rx_if.read_i <= 1'b0;
  endtask : rx_read_data


//--------//
//  MAIN  //
//--------//

  task main();
    forever begin
      if (rx_if.rx_done_o) begin 
        $display("[RX Driver][%0dns] Data received", $time); 
        rx_read_data();
        ->rxDone_ev;
      end
    end
  endtask : main 

endclass : uart_rx_driver

`endif