`ifndef UART_DRIVER
  `define UART_DRIVER

`include "uart_trx.sv"
`include "uart_interface.sv"

import UART_pkg::*;
import registers_pkg::*;

class uart_driver;

  /* Transmitter connected to DUT signals */
  tx_interface tx_if;

  /* DUT interface */
  uart_interface uart_if;

  mailbox gen2drv_mbx;
  mailbox drv2mon_mbx;

  event drvDone_ev;
  event txDone_ev;

  uart_trx pkt;

  bit [7:0] data;


//---------------//
//  CONSTRUCTOR  //
//---------------//

  function new(input virtual uart_interface uart_if, input mailbox gen2drv, input mailbox drv2mon, input event drvDone, input virtual tx_interface tx_if);
    this.uart_if = uart_if;
    this.tx_if = tx_if;
    this.gen2drv_mbx = gen2drv;
    this.drv2mon_mbx = drv2mon;
    this.drvDone_ev = drvDone;
    this.pkt = new();
  endfunction : new


//---------//
//  TASKS  //
//---------//

  /* 
   *  Reset the DUT, used in the pre test 
   */
  task reset();
    wait(!uart_if.rst_n_i);
    $display("[Driver][%0dns] Resetting DUT and transmitter...", $time); 
    tx_if.reset();
    uart_if.reset();
    wait(uart_if.rst_n_i);
    $display("[Driver][%0dns] Reset completed!", $time); 
  endtask : reset

  /* 
   *  Basic task of transmitter module 
   */
  task drive_rx_port();
    forever begin 
      /* Assign configuration */
      tx_if.data_width_i <= pkt.data_width;
      tx_if.stop_bits_i <= pkt.stop_bits;
      tx_if.parity_mode_i <= pkt.parity_mode;

      /* Write TX FIFO, then wait for the transmitter
       * to end its task */
      tx_if.tx_fifo_write_i <= !tx_if.tx_fifo_full_o;
      tx_if.data_tx_i <= $urandom();
      @(posedge tx_if.clk_i);
      tx_if.tx_fifo_write_i <= 1'b0;
      
      $display("[Driver][%0dns] Transmitter is sending data...", $time); 
      wait(tx_if.tx_done_o);
      $display("[Driver][%0dns] Transmission done!", $time); 
      ->txDone_ev;
    end
  endtask : drive_rx_port


  /* 
   *  Send configuration request 
   */
  task tx_config_req();
    $display("[Driver][%0dns] Sending configuration request", $time); 
    tx_if.config_req_mst_i <= 1'b1;
    @(posedge tx_if.clk_i);
    tx_if.config_req_mst_i <= 1'b0;
    wait(tx_if.req_done_o);
    $display("[Driver][%0dns] Request completed", $time); 
  endtask : tx_config_req

  
  /* 
   *  Drive the uart based on the operation  
   */
  task uart_drive();
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

        CHANGE_CONFIG: begin 
          uart_config_change();
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

        NO_OPERATION: begin 
          repeat(20) @(posedge uart_if.clk_i);
        end
      endcase
    end  
  endtask : uart_drive


  /* 
   *  Read a register 
   */
  task uart_read_register(input bit [2:0] address, output bit [7:0] data);
    uart_if.address_i <= address;
    uart_if.read_i <= 1'b1;
    @(posedge uart_if.clk_i);
    uart_if.read_i <= 1'b0;
    data <= uart_if.data_io;
    $display("[Driver][%0dns] Register %0d read: 0x%0h", $time, address, data); 
  endtask : uart_read_register


  /* 
   *  Write a register 
   */
  task uart_write_register(input bit [2:0] address, input bit [7:0] data);
    $display("[Driver][%0dns] Writing data 0x%0h into register %0d", $time, data, address); 
    uart_if.address_i <= address;
    uart_if.write_i <= 1'b1;
    uart_if.data_io <= data;
    @(posedge uart_if.clk_i);
    uart_if.write_i <= 1'b0;
    $display("[Driver][%0dns] Register written!", $time); 
  endtask : uart_write_register


  /* 
   *  Read data from RXR register 
   */
  task uart_read_RXdata(output bit [7:0] data);
    FSR_data_t temp_data;

    /* Assert that RX FIFO is not empty */
    uart_if.address_i <= FSR_ADDR;
    uart_if.read_i <= 1'b1;
    @(posedge uart_if.clk_i);
    uart_if.read_i <= 1'b0;
    temp_data <= uart_if.data_io;

    /* If it's not empty read the register */
    if (!temp_data.RXE) begin 
      uart_read_register(RXR_ADDR, data);
    end
  endtask : uart_read_RXdata


  /* 
   *  Write data into TXR register 
   */
  task uart_write_TXdata(input bit [7:0] data);
    FSR_data_t temp_data;

    /* Assert that TX FIFO is not full */
    uart_if.address_i <= FSR_ADDR;
    uart_if.read_i <= 1'b1;
    @(posedge uart_if.clk_i);
    uart_if.read_i <= 1'b0;
    temp_data <= uart_if.data_io;

    /* If it's not full write the register */
    if (!temp_data.TXF) begin 
      uart_write_register(TXR_ADDR, data);
    end
  endtask : uart_write_TXdata


  /* 
   *  Modify UART configuration 
   */
  task uart_config_change();
    $display("[Driver][%0dns] Changing configuration...", $time); 

    /* Read STR and modify if, then write it back */
    FSR_data_t temp_data;
    uart_read_register(STR_ADDR, temp_data); 
    temp_data[5:0] <= {$urandom_range(3), $urandom_range(3), $urandom_range(3)};
    $display("[Driver][%0dns] Data Width %0b", $time, temp_data[1:0]); 
    $display("[Driver][%0dns] Parity Mode %0b", $time, temp_data[3:2]); 
    $display("[Driver][%0dns] Stop Bits %0b", $time, temp_data[5:4]); 
    uart_write_register(STR_ADDR, temp_data);
  endtask : uart_config_change


  /* 
   *  Set RX FIFO interrupt threshold value 
   */
  task uart_set_threshold();
    $display("[Driver][%0dns] Modifing threshold...", $time); 

    FSR_data_t temp_data;
    uart_read_register(FSR_ADDR, temp_data);
    temp_data.RX_TRESHOLD <= $urandom_range(63);
    $display("[Driver][%0dns] Threshold new value: %0d", $time, temp_data.RX_TRESHOLD); 
    uart_write_register(FSR_ADDR, temp_data);
  endtask : uart_set_threshold


  /* 
   *  Set communication mode 
   */
  task uart_set_communication_mode();
    CTR_data_t temp_data;
    uart_read_register(CTR_ADDR, temp_data);
    temp_data.COM <= $urandom_range(3);
    uart_write_register(CTR_ADDR, temp_data);
  endtask : uart_set_communication_mode


  /* 
   *  Enable or disable receiving configuration requests 
   */
  task uart_enable_config_req();
    CTR_data_t temp_data;
    uart_read_register(CTR_ADDR, temp_data);
    temp_data.ENREQ <= $urandom_range(1);
    $display("[Driver][%0dns] Configuration request %0s", $time, temp_data.ENREQ ? "enabled" : "disabled"); 
    uart_write_register(CTR_ADDR, temp_data);
  endtask : uart_enable_config_req


  /* 
   *  Enable or disable interrupt sources
   */
  task uart_enable_interrupt();
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
  task uart_read_intID(output bit [2:0] id);
    ISR_data_t temp_data;
    uart_read_register(ISR_ADDR, temp_data);
    id <= temp_data.INTID; 
    $display("[%0dns] Interrupt ID: 0x%0h", $time, temp_data.INTID); 
  endtask : uart_read_intID


  /* 
   *  Clear interrupt 
   */
  task uart_clear_interrupt(output bit [7:0] data_read[64]);
    bit [2:0] id;
    bit [7:0] data[];
    uart_read_intID(id);

    case (id)
      INT_TX_DONE: begin 
        bit [7:0] temp_data;

        /* Set acknowledge bit */
        uart_read_register(ISR_ADDR, temp_data);
        data[0] <= 1'b1;
        uart_write_register(ISR_ADDR, temp_data);
      end

      INT_CONFIG_FAIL: begin 
        bit [7:0] temp_data;

        /* Set acknowledge bit */
        uart_read_register(ISR_ADDR, temp_data);
        data[0] <= 1'b1;
        uart_write_register(ISR_ADDR, temp_data);      
      end

      INT_CONFIG_REQ: begin 
        bit [7:0] temp_data;

        /* Set acknowledge bit */
        uart_read_register(ISR_ADDR, temp_data);
        data[0] <= 1'b1;
        uart_write_register(ISR_ADDR, temp_data);      
      end

      INT_OVERRUN: begin 
        data = new[1];
        uart_read_RXdata(data[0]);
      end

      INT_PARITY: begin 
        data = new[1];
        uart_read_RXdata(data[0]);
      end

      INT_FRAME: begin 
        data = new[1];
        uart_read_RXdata(data[0]);
      end

      INT_RXD_RDY: begin 
        bit [7:0] temp_data;
        uart_read_register(STR_ADDR, temp_data);

        /* Check if RX data stream mode is enabled */
        if (temp_data[6]) begin 
          /* Generate an array able to store all 
           * the buffer data */
          uart_read_register(FSR_ADDR, temp_data);
          data = new[temp_data[5:0]];

          /* Read until RX buffer is empty */
          for (int i = 0; temp_data[6] == 1'b1; i++) begin 
            uart_read_RXdata(data[i]);
          end
        end else begin
          data = new[1];
          uart_read_RXdata(data[0]);
        end
      end

      INT_RX_FULL: begin 
        /* Read until RX buffer is empty */
        for (int i = 0; i < 64; i++) begin 
          uart_read_RXdata(data[i]);
        end        
      end
    endcase
  endtask : uart_clear_interrupt


//--------//
//  MAIN  //
//--------//

  task main();
    fork 
      
    join
  endtask : main 

endclass : uart_driver

`endif 