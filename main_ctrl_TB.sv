`include "main_ctrl_Interface.sv"

module main_ctrl_TB();

//---------------------//
//  DUT INSTANTIATION  //
//---------------------//

  bit clk_i, rst_n_i;

  /* Clock generation */
  always #5 clk_i = !clk_i;

  main_ctrl_Interface intf(clk_i);

  main_controller DUT (
    .clk_i                 ( intf.clk_i                 ),
    .rst_n_i               ( intf.rst_n_i               ),
    .interrupt_ackn_i      ( intf.interrupt_ackn_i      ),
    .data_rx_i             ( intf.data_rx_i             ),
    .data_tx_i             ( intf.data_tx_i             ),
    .tx_done_i             ( intf.tx_done_i             ),
    .req_done_i            ( intf.req_done_i            ),
    .frame_error_i         ( intf.frame_error_i         ),
    .parity_i              ( intf.parity_i              ),
    .overrun_error_i       ( intf.overrun_error_i       ), 
    .configuration_error_i ( intf.configuration_error_i ),    
    .rx_fifo_empty_i       ( intf.rx_fifo_empty_i       ),
    .tx_fifo_empty_i       ( intf.tx_fifo_empty_i       ),
    .rx_fifo_read_i        ( intf.rx_fifo_read_i        ),
    .tx_fifo_write_i       ( intf.tx_fifo_write_i       ),
    .config_req_slv_i      ( intf.config_req_slv_i      ),
    .config_req_mst_i      ( intf.config_req_mst_i      ),
    .std_config_i          ( intf.std_config_i          ),
    .config_i              ( intf.config_i              ),
    .data_stream_mode_i    ( intf.data_stream_mode_i    ),
    .req_ackn_i            ( intf.req_ackn_i            ),
    .STR_en_o              ( intf.STR_en_o              ),
    .config_o              ( intf.config_o              ),
    .config_req_mst_o      ( intf.config_req_mst_o      ),
    .data_stream_mode_o    ( intf.data_stream_mode_o    ),
    .configuration_done_o  ( intf.configuration_done_o  ),
    .req_ackn_o            ( intf.req_ackn_o            ),
    .rx_fifo_read_o        ( intf.rx_fifo_read_o        ),
    .tx_fifo_write_o       ( intf.tx_fifo_write_o       ),
    .data_tx_o             ( intf.data_tx_o             ),
    .error_o               ( intf.error_o               )
  );


//------------------//
//  TESTBENCH BODY  //
//------------------//

  main_ctrl_Transaction trxPacket;

  /* To simulate rx buffer */
  bit [7:0] rxBuffer [$:UART_pkg::RX_FIFO_DEPTH];
  bit [7:0] trashValue;

  task reset();
    $display("[%0tns] Resetting DUT...", $time);
    intf.rst_n_i <= 1'b0;
    intf.reset();
    @(posedge intf.clk_i);
    intf.rst_n_i <= 1'b1;
    $display("[%0dns] Reset completed", $time); 
  endtask : reset 

  task sendConfigReq();
    $display("[%0dns] Sending configuration request...", $time);  
    @(posedge intf.clk_i);
    $display("[%0dns] Finished driving low tx line for 10ms", $time); 
    
    intf.req_done_i <= 1'b1;
    intf.config_req_mst_i <= 1'b0;
    @(posedge intf.clk_i);
  endtask : sendConfigReq 

 
  /* Drive transactions when the uart is in main state */
  task deviceMainState(input int trxNumber);
    repeat(trxNumber) begin 
      assert(trxPacket.randomize())
      else $error("[%0dns] Failed randomization", $time);
 
      /* Drive the signals that are useful during main state */
      $display("[%0dns] Driving transaction...", $time);
      intf.data_tx_i <= trxPacket.data.data_tx_i;
      intf.frame_error_i <= trxPacket.frame_error_i;
      intf.parity_i <= trxPacket.data.parity_i;
      intf.overrun_error_i <= trxPacket.overrun_error_i;
      intf.rx_fifo_read_i <= trxPacket.data.rx_fifo_read_i;
      intf.tx_fifo_write_i <= trxPacket.data.tx_fifo_write_i;

      rxBuffer.push_back(trxPacket.data.data_rx_i);
      if (trxPacket.data.rx_fifo_read_i) begin 
        intf.data_rx_i <= rxBuffer.pop_front();
      end

      /* Empty logic */
      if (rxBuffer.size() == 0) begin
        intf.rx_fifo_empty_i <= 1'b1;
      end else begin 
        intf.rx_fifo_empty_i <= 1'b0;
      end

      trxPacket.data.data_tx_o = intf.data_tx_o;
      trxPacket.error_o = intf.error_o;

      assert(trxPacket.data.data_tx_i == trxPacket.data.data_tx_o)
      else $error("[%0dns] Data tx output mismatch!", $time); 

      if (trxPacket.frame_error_i | trxPacket.data.inject_error | trxPacket.overrun_error_i) begin 
        assert(trxPacket.error_o != 0)
        else $error("[%0dns] Error not detected!", $time); 
      end
      /* Data received and transmitted is processed in more than 1 clock cycle, but
       * the controller is not dependant on baud rate clock */
      @(posedge intf.clk_i);
    end
  endtask : deviceMainState


  /* Uart has requested a configuration setup */
  task deviceConfigSetupMaster();
    /* Send configuration request, after 10ms the driver will respond to the request */
    intf.config_req_mst_i <= 1'b1;
    intf.rx_fifo_empty_i <= 1'b1;
    sendConfigReq();
    intf.req_done_i <= 1'b0; 

    $display("[%0dns] Waiting for acknowledgement packet...", $time); 
    intf.req_done_i <= 1'b0;
    intf.data_rx_i <= ACKN_PKT;
    intf.rx_fifo_empty_i <= 1'b0;
    @(posedge intf.clk_i);


    /* Repeat 4 times to send all the packets */
    $display("[%0dns] Acknowledgement received, sending configuration packets...", $time); 
    for (int i = 0; i < 4; i++) begin 
      /* (SETUP_MST state) */
      $display("[%0dns] Waiting for transmitter to send data...", $time); 
      intf.rx_fifo_empty_i <= 1'b1;
      @(posedge intf.clk_i);

      /* (WAIT_TX_MST state) */
      $display("[%0dns] Configuration packet sended", $time); 
      intf.tx_done_i <= 1'b1;
      @(posedge intf.clk_i);
      
      trxPacket.data.data_tx_o = intf.data_tx_o;
      case(i)
        0: assert(trxPacket.data.data_tx_o == assemble_packet(DATA_WIDTH_ID, STD_DATA_WIDTH));
        1: assert(trxPacket.data.data_tx_o == assemble_packet(PARITY_MODE_ID, STD_PARITY_MODE));
        2: assert(trxPacket.data.data_tx_o == assemble_packet(STOP_BITS_ID, STD_STOP_BITS));
        3: assert(trxPacket.data.data_tx_o == assemble_packet(END_CONFIGURATION_ID, 2'b0)); 
      endcase

      /* (WAIT_ACKN_MST state) */
      $display("[%0dns] Waiting for acknowledgement packet...", $time); 
      intf.tx_done_i <= 1'b0;
      intf.data_rx_i <= ACKN_PKT;
      intf.rx_fifo_empty_i <= 1'b0;
      @(posedge intf.clk_i);
    end

    /* Main state */
  endtask : deviceConfigSetupMaster


  /* Driver send a configuration request to the uart */
  task deviceConfigSetupSlave();
    intf.config_req_slv_i <= 1'b1;
    $display("[%0dns] Configuration request received", $time); 
    @(posedge intf.clk_i);

    intf.req_ackn_i <= 1'b1;
    $display("[%0dns] Request acknowledged", $time); 
    repeat(2) @(posedge intf.clk_i);

    trxPacket.data.data_tx_o = intf.data_tx_o;
    assert(trxPacket.data.data_tx_o == ACKN_PKT)
    else $error("[%0dns] Acknowledge packet not sended", $time); 

    /* Done transmitting the acknowledgment packet */
    intf.req_ackn_i <= 1'b0;
    intf.tx_done_i <= 1'b1;

    /* Receive configuration packet */
    for (int i = 0; i < 4; i++) begin 
      @(posedge intf.clk_i);
      /* (SETUP_SLV state) */
      intf.tx_done_i <= 1'b0;
      case(i)  
        0: intf.data_rx_i <= assemble_packet(DATA_WIDTH_ID, STD_DATA_WIDTH);
        1: intf.data_rx_i <= assemble_packet(PARITY_MODE_ID, STD_PARITY_MODE);
        2: intf.data_rx_i <= assemble_packet(STOP_BITS_ID, STD_STOP_BITS);
        3: intf.data_rx_i <= assemble_packet(END_CONFIGURATION_ID, 2'b00);
      endcase
      intf.rx_fifo_empty_i <= 1'b0;
      $display("[%0dns] Received configuration packet", $time); 
      @(posedge intf.clk_i);

      /* (SEND_ACKN_SLV state) */
      $display("[%0dns] Sending acknowledgemnt packet", $time); 
      intf.rx_fifo_empty_i <= 1'b1;
      @(posedge intf.clk_i);
      assert(intf.data_tx_o == ACKN_PKT)
      else $error("[%0dns] Acknowledge packet not sended", $time);

      /* Transmitter has done its task (WAIT_TX_SLV state) */
      intf.tx_done_i <= 1'b1;
    end

    /* Main state */
  endtask : deviceConfigSetupSlave


//--------//
//  MAIN  //
//--------//

  /* Reset the device and verify it's behaviour in main state. Send a configuration
   * request as a master,  */
  initial begin
    trxPacket = new();
    reset();
    deviceMainState(25);
    deviceConfigSetupMaster();
    deviceMainState(5);
    deviceConfigSetupSlave();
    deviceMainState(5);
    $finish;
  end

endmodule 