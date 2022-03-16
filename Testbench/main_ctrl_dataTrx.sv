`ifndef MAIN_CTRL_DATA_TRX_SV
  `define MAIN_CTRL_DATA_TRX_SV

class main_ctrl_dataTrx;

  rand  logic [7:0] data_tx_i;
  rand  logic [7:0] data_rx_i;
  logic [7:0]       data_tx_o;
  logic             parity_i;

  logic             rx_fifo_empty_i;
  logic             tx_fifo_empty_i;
  logic             rx_fifo_read_i;
  logic             tx_fifo_write_i;
  logic             rx_fifo_read_o;
  logic             tx_fifo_write_o;

  rand logic        inject_error;

//------------//
// CONSTRAINT //
//------------//

  constraint inject_error_c { inject_error dist {1'b0 := 80, 1'b1 := 20}; }

//-------------//
// CONSTRUCTOR //
//-------------//

  function new();
    data_tx_i = 'b0;
    data_rx_i = 'b0;
    data_tx_o = 'b0;
    parity_i = 1'b0;

    rx_fifo_empty_i = 1'b0;
    tx_fifo_empty_i = 1'b0;
    rx_fifo_read_i = 1'b0;
    tx_fifo_write_i = 1'b0;
    rx_fifo_read_o = 1'b0;
    tx_fifo_write_o = 1'b0;

    inject_error = 1'b0;
  endfunction : new

//-----------//
// FUNCTIONS //
//-----------//

  /* Calculate parity on received data */
  function automatic bit calc_parity (input logic [1:0] parity_type);
    bit p_even = ^this.data_rx_i ^ 1'b0;
    bit p_odd = ^this.data_rx_i ^ 1'b1;

    if (parity_type == UART_pkg::EVEN) begin
      return this.inject_error ? !p_even : p_even;
    end else if (parity_type == UART_pkg::ODD) begin
      return this.inject_error ? !p_odd : p_odd;
    end else begin
      return 1'b0;
    end
  endfunction : calc_parity

  /* Print fifo status */
  function void displayFifoStatus(input string tag);
    $display("[%0s] [%0dns] RX FIFO:  EMPTY = %0b  |  READ IN = %0b   |  READ OUT = %0b", tag, $time, rx_fifo_empty_i, rx_fifo_read_i, rx_fifo_read_o);
    $display("[%0s] [%0dns] TX FIFO:  EMPTY = %0b  |  WRITE IN = %0b  |  WRITE OUT = %0b", tag, $time, tx_fifo_empty_i, tx_fifo_read_i, tx_fifo_read_o);
  endfunction : displayFifoStatus

  /* Print data information */
  function void displayData(input string tag);
    $display("[%0s] [%0dns] RX DATA:  VALUE IN = 0x%h  |  PARITY = %0b", tag, $time, data_rx_i, parity_i);
    $display("[%0s] [%0dns] TX DATA:  VALUE IN = 0x%h  |  VALUE OUT = 0x%h", tag, $time, data_rx_i, data_rx_o);
  endfunction : displayData

endclass : main_ctrl_dataTrx

`endif 
