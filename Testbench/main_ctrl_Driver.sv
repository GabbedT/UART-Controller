`ifndef MAIN_CTRL_DRIVER_SV
  `define MAIN_CTRL_DRIVER_SV  

`include "main_ctrl_Interface.sv"

class main_ctrl_Driver #(parameter DEBUG = 1);

  main_ctrl_Transaction trxPacket;

  virtual main_ctrl_interface vif;

  /* Driver has done driving the transaction */
  event drvDone_ev;

  /* To receive packets from generator */
  mailbox gen2drv_mbx; 

  /* To simulate rx buffer */
  bit [7:0] rxBuffer [$:UART_pkg::RX_FIFO_DEPTH];
  bit [7:0] trashValue;


//-------------//
// CONSTRUCTOR //
//-------------//

  function new(input virtual main_ctrl_interface vif, input event drvDone_ev, input mailbox gen2drv_mbx);
    this.vif = vif;
    this.drvDone_ev = drvDone_ev;
    this.gen2drv_mbx = gen2drv_mbx;
    this.trxPacket = new();
  endfunction : new 


//-----------//
// FUNCTIONS //
//-----------//


  task reset();
    wait(!vif.drv_cb.rst_n_i);
    @(posedge vif.clk_i);
    vif.reset();
  endtask : reset 


  task sendConfigReq();
    vif.drv_cb.config_req_mst_i <= 1'b1;
    repeat(COUNT_10MS) @(posedge vif.clk_i);
    vif.drv_cb.req_done_i <= 1'b1;
    @(posedge vif.clk_i);
  endtask : sendConfigReq 


  /* Drive transactions when the uart is in main state */
  task deviceMainState(input int trxNumber);
    repeat(trxNumber) begin 
      /* Drive the signals that are useful during main state */
      vif.drv_cb.data_tx_i <= trxPacket.data.data_tx_i;
      vif.drv_cb.frame_error_i <= trxPacket.data.frame_error_i;
      vif.drv_cb.parity_i <= trxPacket.data.parity_i;
      vif.drv_cb.overrun_error_i <= trxPacket.data.overrun_error_i;
      vif.drv_cb.rx_fifo_read_i <= trxPacket.data.rx_fifo_read_i;
      vif.drv_cb.tx_fifo_write_i <= trxPacket.data.tx_fifo_write_i;

      rxBuffer.push_back(trxPacket.data.data_rx_i);
      if (trxPacket.data.rx_fifo_read_i) begin 
        vif.drv_cb.data_rx_i <= rxBuffer.pop_front();
      end

      /* Empty logic */
      if (rxBuffer.size() == 0) begin
        vif.drv_cb.rx_fifo_empty_i <= 1'b1;
      end else begin 
        vif.drv_cb.rx_fifo_empty_i <= 1'b0;
      end

      assert(trxPacket.data.data_tx_i == vif.drv_cb.data_tx_o);
      if (vif.drv_cb.frame_error_i | trxPacket.data.inject_error | vif.drv_cb.overrun_error_i) begin 
        assert(vif.drv_cb.error_o != 0);
      end
      /* Data received and transmitted is processed in more than 1 clock cycle, but
       * the controller is not dependant on baud rate clock */
      @(posedge vif.clk_i);
    end
  endtask : deviceMainState


  /* Uart has requested a configuration setup */
  task deviceConfigSetupMaster();
    /* Send configuration request, after 10ms the driver will respond to the request */
    sendConfigReq();
    vif.drv_cb.config_req_mst_i <= 1'b0;

    /* Miss acknowledgment */
    repeat(COUNT_50MS) @(posedge vif.clk_i); 
    assert(vif.drv_cb.config_req_mst_o);

    repeat(COUNT_10MS) @(posedge vif.clk_i);
    vif.drv_cb.req_done_i <= 1'b1;
    @(posedge vif.clk_i);

    /* Waiting for acknowledgement packet */
    vif.drv_cb.req_done_i <= 1'b0;
    vif.drv_cb.data_rx_i <= ACKN_PKT;
    vif.drv_cb.rx_fifo_empty_i <= 1'b0;
    @(posedge vif.clk_i);


    /* Repeat 4 times to send all the packets */
    for (int i = 0; i < 4; i++) begin 
      /* Waiting for transmitter to send data (SETUP_MST state) */
      vif.drv_cb.rx_fifo_empty_i <= 1'b1;
      @(posedge vif.clk_i);

      /* The transmitter has sended the configuration packet (WAIT_TX_MST state) */
      vif.drv_cb.tx_done_i <= 1'b1;
      @(posedge vif.clk_i);
      case(i)
        0: assert(vif.drv_cb.data_tx_o == assemble_packet(DATA_WIDTH_ID, STD_DATA_WIDTH));
        1: assert(vif.drv_cb.data_tx_o == assemble_packet(PARITY_MODE_ID, STD_PARITY_MODE));
        2: assert(vif.drv_cb.data_tx_o == assemble_packet(STOP_BITS_ID, STD_STOP_BITS));
        3: assert(vif.drv_cb.data_tx_o == assemble_packet(END_CONFIGURATION_ID, 2'b0)); 
      endcase

      /* Waiting for acknowledgement packet (WAIT_ACKN_MST state) */
      vif.drv_cb.tx_done_i <= 1'b0;
      vif.drv_cb.data_rx_i <= ACKN_PKT;
      vif.drv_cb.rx_fifo_empty_i <= 1'b0;
      @(posedge vif.clk_i);
    end

    /* Main state */
  endtask : deviceConfigSetupMaster


  /* Driver send a configuration request to the uart */
  task deviceConfigSetupSlave();
    vif.drv_cb.config_req_slv_i <= 1'b1;
    @(posedge vif.clk_i);

    vif.drv_cb.req_ackn_i <= 1'b1;
    repeat(2) @(posedge vif.clk_i);

    /* Done transmitting the acknowledgment packet */
    vif.drv_cb.req_ackn_i <= 1'b0;
    vif.drv_cb.tx_done_i <= 1'b1;
    @(posedge vif.clk_i);

    /* Receive configuration packet */
    for (int i = 0; i < 4; i++) begin 
      /* Receive packet (SETUP_SLV state) */
      vif.drv_cb.tx_done_i <= 1'b0;
      case(i)  
        0: vif.drv_cb.data_rx_i <= assemble_packet(DATA_WIDTH_ID, STD_DATA_WIDTH);
        1: vif.drv_cb.data_rx_i <= assemble_packet(PARITY_MODE_ID, STD_PARITY_MODE);
        2: vif.drv_cb.data_rx_i <= assemble_packet(STOP_BITS_ID, STD_STOP_BITS);
        3: vif.drv_cb.data_rx_i <= assemble_packet(END_CONFIGURATION_ID, 2'b00);
      endcase
      vif.drv_cb.rx_fifo_empty_i <= 1'b0;
      @(posedge vif.clk_i);

      /* Send acknowledgemnt packet (SEND_ACKN_SLV state) */
      vif.drv_cb.rx_fifo_empty_i <= 1'b1;
      @(posedge vif.clk_i);
      assert(vif.drv_cb.data_tx_o == ACKN_PKT);

      /* Transmitter has done its task (WAIT_TX_SLV state) */
      vif.drv_cb.tx_done_i <= 1'b1;
      @(posedge vif.clk_i);
    end

    /* Main state */
  endtask : deviceConfigSetupSlave


  task run();
    reset();
    deviceMainState(25);
    deviceConfigSetupMaster();
    deviceMainState(5);
    deviceConfigSetupSlave();
    deviceMainState(5);
  endtask : run

endclass : main_ctrl_Driver

`endif