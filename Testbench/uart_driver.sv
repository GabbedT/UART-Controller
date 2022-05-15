`ifndef UART_DRIVER
  `define UART_DRIVER

`include "uart_trx.sv"
`include "uart_interface.sv"

import UART_pkg::*;
import registers_pkg::*;

class uart_driver;

  /* Receiver */
  uart_rx_driver rx;
  rx_interface rx_if;
  mailbox rx2mon_mbx;
  event rxDone_ev;

  /* Transmitter */
  uart_tx_driver tx;
  tx_interface tx_if;
  mailbox tx2mon_mbx;
  event txDone_ev;

  /* DUT */
  uart_interface uart_if;

  /* Driver */
  mailbox gen2drv_mbx;
  event drvDone_ev;
  uart_trx pkt;


//---------------//
//  CONSTRUCTOR  //
//---------------//

  function new(input virtual uart_interface uart_if, input mailbox gen2drv_mbx, input event drvDone_ev,
               input virtual rx_interface rx_if, input mailbox rx2mon_mbx, input event rxDone_ev,
               input virtual tx_interface tx_if, input mailbox tx2mon_mbx, input event txDone_ev);

    this.uart_if = uart_if;
    this.tx_if = tx_if;
    this.rx_if = rx_if;

    this.gen2drv_mbx = gen2drv;
    this.rx2mon_mbx = rx2mon_mbx;
    this.tx2mon_mbx = tx2mon_mbx;

    this.drvDone_ev = drvDone;
    this.rxDone_ev = rxDone_ev;
    this.txDone_ev = txDone_ev;

    this.pkt = new();

    this.rx = new(rx_if, rx2mon_mbx, rxDone_ev);
    this.tx = new(tx_if, tx2mon_mbx, txDone_ev);
  endfunction : new


//---------//
//  TASKS  //
//---------//

  /* 
   *  Reset the DUT, used in the pre test 
   */
  task automatic reset();
    wait(!uart_if.rst_n_i);
    $display("[Driver][%0dns] Resetting DUT and transmitter...", $time); 
    tx_if.reset();
    rx_if.reset();
    uart_if.reset();
    wait(uart_if.rst_n_i);
    $display("[Driver][%0dns] Reset completed!", $time); 
  endtask : reset

  
  /* 
   *  Drive the uart based on the operation  
   */
  task automatic uart_drive();
    forever begin
      if (pkt.operation != NO_OPERATION) begin 
        ++pkt.coverage[pkt.operation];
      end 

      case (pkt.operation)
        READ_DATA: begin 
          uart_read_RXdata(data);
        end

        SEND_DATA: begin 
          uart_write_TXdata($urandom());
        end

        SEND_DATA_BURST: begin 
          uart_send_burst($urandom_range(63));
        end

        SET_THRESHOLD: begin 
          uart_set_threshold();
        end

        SET_COM_MODE: begin 
          uart_set_communication_mode();
        end

        ENABLE_CONFIG_REQ: begin 
          uart_enable_config_req();
        end

        ENABLE_INTERRUPT: begin 
          uart_enable_interrupt();
        end

        SEND_DATA_BURST: begin 
          uart_send_burst($urandom_range(UART_pkg::TX_FIFO_DEPTH));
        end

        NO_OPERATION: begin 
          repeat(20) @(posedge uart_if.clk_i);
        end
      endcase
    end  
  endtask : uart_drive


  /* 
   *  Read a register 
   */
  task automatic uart_read_register(input bit [2:0] address, output bit [7:0] data);
    uart_if.address_i <= address;
    uart_if.read_write_i <= READ;
    uart_if.enable_chip();
    data <= uart_if.data_io;
    @(posedge uart_if.clk_i);

    uart_if.disable_chip();
    $display("[Driver][%0dns] Register %0d read: 0x%0h", $time, address, data); 
  endtask : uart_read_register


  /* 
   *  Write a register 
   */
  task automatic uart_write_register(input bit [2:0] address, input bit [7:0] data);
    $display("[Driver][%0dns] Writing data 0x%0h into register %0d", $time, data, address); 
    uart_if.address_i <= address;
    uart_if.read_write_i <= WRITE;
    uart_if.data_io <= data;
    uart_if.enable_chip();
    @(posedge uart_if.clk_i);

    uart_if.disable_chip();
    $display("[Driver][%0dns] Register written!", $time); 
  endtask : uart_write_register


  /* 
   *  Read data from RXR register 
   */
  task automatic uart_read_RXdata(output bit [7:0] data);
    FSR_data_t temp_data;

    /* Assert that RX FIFO is not empty */
    uart_if.address_i <= FSR_ADDR;
    uart_if.read_write_i <= READ;
    uart_if.enable_chip();
    temp_data <= uart_if.data_io;
    @(posedge uart_if.clk_i);

    uart_if.disable_chip();

    /* If it's not empty read the register */
    if (!temp_data.RXE) begin 
      uart_read_register(RXR_ADDR, data);
    end else begin 
      $display("[Driver][%0dns] RX FIFO empty!", $time); 
    end
  endtask : uart_read_RXdata


  /* 
   *  Write data into TXR register 
   */
  task automatic uart_write_TXdata(input bit [7:0] data);
    FSR_data_t temp_data;

    /* Assert that TX FIFO is not full */
    uart_if.address_i <= FSR_ADDR;
    uart_if.read_write_i <= READ;
    uart_if.enable_chip();
    temp_data <= uart_if.data_io;
    @(posedge uart_if.clk_i);
    uart_if.disable_chip();

    /* If it's not full write the register */
    if (!temp_data.TXF) begin 
      uart_write_register(TXR_ADDR, data);
    end else begin 
      $display("[Driver][%0dns] TX FIFO full!", $time); 
    end
  endtask : uart_write_TXdata


  /* 
   *  Set RX FIFO interrupt threshold value 
   */
  task automatic uart_set_threshold();
    FSR_data_t temp_data;
    $display("[Driver][%0dns] Modifing threshold...", $time); 

    uart_read_register(FSR_ADDR, temp_data);
    temp_data.RX_TRESHOLD <= $urandom_range(63);
    $display("[Driver][%0dns] Threshold new value: %0d", $time, temp_data.RX_TRESHOLD); 
    uart_write_register(FSR_ADDR, temp_data);
  endtask : uart_set_threshold


  /* 
   *  Set communication mode 
   */
  task automatic uart_set_communication_mode();
    CTR_data_t temp_data;
    uart_read_register(CTR_ADDR, temp_data);
    temp_data.COM <= $urandom_range(3);
    uart_write_register(CTR_ADDR, temp_data);
  endtask : uart_set_communication_mode


  /* 
   *  Enable or disable receiving configuration requests 
   */
  task automatic uart_enable_config_req();
    CTR_data_t temp_data;
    uart_read_register(CTR_ADDR, temp_data);
    temp_data.ENREQ <= $urandom_range(1);
    $display("[Driver][%0dns] Configuration request %0s", $time, temp_data.ENREQ ? "enabled" : "disabled"); 
    uart_write_register(CTR_ADDR, temp_data);
  endtask : uart_enable_config_req


  /* 
   *  Enable or disable interrupt sources
   */
  task automatic uart_enable_interrupt();
    ISR_data_t temp_data;
    uart_read_register(ISR_ADDR, temp_data);
    temp_data.RXRDY <= $urandom_range(1);
    temp_data.FRM <= $urandom_range(1);
    temp_data.PAR <= $urandom_range(1);
    temp_data.OVR <= $urandom_range(1);
  endtask : uart_enable_interrupt


  /* 
   *  Read interrupt ID 
   */
  task automatic uart_read_intID(output bit [2:0] id);
    ISR_data_t temp_data;
    uart_read_register(ISR_ADDR, temp_data);
    id <= temp_data.INTID; 
    $display("[%0dns] Interrupt ID: 0x%0h", $time, temp_data.INTID); 
  endtask : uart_read_intID


  /* 
   *  Clear interrupt 
   */
  task automatic uart_clear_interrupt(output bit [7:0] data_read[64]);
    bit [2:0] id;
    bit [7:0] data;
    uart_read_intID(id);

    case (id)
      INT_TX_DONE: begin 
        /* Set acknowledge bit */
        uart_read_register(ISR_ADDR, data);
        data <= 1'b1;
        uart_write_register(ISR_ADDR, data);
      end

      INT_CONFIG_FAIL: begin 
        /* Set acknowledge bit */
        uart_read_register(ISR_ADDR, data);
        data <= 1'b1;
        uart_write_register(ISR_ADDR, data);      
      end

      INT_CONFIG_REQ: begin 
        /* Set acknowledge bit */
        uart_read_register(ISR_ADDR, data);
        data <= 1'b1;
        uart_write_register(ISR_ADDR, data);      
      end

      INT_OVERRUN: begin 
        uart_read_RXdata(data);
      end

      INT_PARITY: begin 
        uart_read_RXdata(data);
      end

      INT_FRAME: begin 
        uart_read_RXdata(data);
      end

      INT_RXD_RDY: begin 
        bit [7:0] temp_data;
        uart_read_register(STR_ADDR, temp_data);

        /* Check if RX data stream mode is enabled */
        if (temp_data[6]) begin 
          uart_read_register(FSR_ADDR, temp_data);

          /* Read until RX buffer is empty */
          for (int i = 0; temp_data[6] == 1'b1; i++) begin 
            uart_read_RXdata(data_read[i]);
          end
        end else begin
          data = new[1];
          uart_read_RXdata(data_read[0]);
        end
      end

      INT_RX_FULL: begin 
        /* Read until RX buffer is empty */
        for (int i = 0; i < 64; i++) begin 
          uart_read_RXdata(data_read[i]);
        end        
      end
    endcase
  endtask : uart_clear_interrupt


  /* 
   *  Write a burst of data by writing the TXR register multiple times  
   */
  task automatic uart_send_burst(input int burst_length);
    for (int i = 0; i < burst_length; i++) begin
      uart_write_TXdata($urandom());
    end
  endtask : uart_send_burst


//--------//
//  MAIN  //
//--------//

  task main();
    fork 
      begin : dut
        uart_drive();
      end : dut 

      begin : rx 
        rx_if.main();
      end : rx 

      begin : tx  
        repeat(256) tx_if.main();
      end : tx 
    join
  endtask : main 

endclass : uart_driver

`endif 