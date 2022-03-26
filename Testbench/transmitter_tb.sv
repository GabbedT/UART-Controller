import UART_pkg::*;

module transmitter_tb();

  /* Inputs */
  logic         clk_i = 0;
  logic         rst_n_i;
  logic         ov_baud_rt_i;
  logic [7:0]   data_tx_i;
  logic         tx_fifo_write_i;
  logic         config_req_mst_i;
  logic [1:0]   data_width_i;
  logic [1:0]   stop_bits_number_i;

  /* Outputs */
  logic         tx_o;
  logic         tx_done_o;      
  logic         req_done_o;
  logic         tx_fifo_empty_o;
  logic         tx_fifo_full_o;

  /* 100MHz clock generation */
  always #5 clk_i = !clk_i;

  /* 115200 bauds generator */
  baud_rate_generator #(16) baud_gen (
    .clk_i        ( clk_i        ),
    .rst_n_i      ( rst_n_i      ),
    .divisor_i    ( 16'd53       ),
    .ov_baud_rt_o ( ov_baud_rt_i )
  );

  /* DUT instantiation */
  transmitter dut (.*);

  bit [7:0] tx_fifo [$:TX_FIFO_DEPTH];

  localparam TX_IDLE = 1;


//-------------//
//  TESTBENCH  //
//-------------//


  initial begin 
    rst_n_i <= 1'b0;
    @(posedge clk_i);
    rst_n_i <= 1'b1;
    config_req_mst_i <= 1'b0;
    data_width_i <= $urandom_range(0, 3);
    stop_bits_number_i <= $urandom_range(0, 1);

    while (tx_fifo.size() != 2) begin 
      sendData($urandom());
    end
    tx_fifo_write_i <= 1'b0;

    sendReq();
    $finish;
  end

//---------//
//  TASKS  //
//---------//


  task sendData(input logic [7:0] data);
    data_tx_i <= data;
    tx_fifo_write_i <= 1'b1;
    tx_fifo.push_back(data);
    @(posedge clk_i);
  endtask : sendData


  task sendReq();
    config_req_mst_i <= 1'b1;
    while (!req_done_o) @(posedge clk_i);
    config_req_mst_i <= 1'b0;
  endtask : sendReq

endmodule : transmitter_tb