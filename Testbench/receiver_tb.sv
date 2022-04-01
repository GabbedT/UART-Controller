import UART_pkg::*;

module receiver_tb;

  /* Inputs */
  logic         clk_i = 0;
  logic         rst_n_i;
  logic         ov_baud_rt_i;
  logic         rx_i;
  logic         rx_fifo_read_i;
  logic         req_ackn_i;
  logic [5:0]   threshold_i;
  logic         data_stream_mode;
  logic [1:0]   data_width_i;
  logic [1:0]   stop_bits_number_i;
  logic [1:0]   parity_mode_i;
  
  /* Outputs */
  logic         rx_fifo_full_o;
  logic         rx_fifo_empty_o;
  logic         config_req_slv_o;
  logic         overrun_error_o;
  logic         frame_error_o;
  logic         parity_o;
  logic         rx_done_o;
  logic         rxd_rdy_interrupt_o;
  logic [7:0]   data_rx_o;


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
  receiver dut (.*);

  logic tick;
  bd_counter counter (.*);

  localparam RX_IDLE = 1;
  localparam COUNT_10MS = SYSTEM_CLOCK_FREQ / 100;

  bit [7:0] test [3:0] = {8'hFF, 8'h01, 8'h00, 8'hCF}; 
  int dbit_cnt;
  int sb_cnt;


//-------------//
//  TESTBENCH  //
//-------------//

  initial begin 
    reset();

    for (int i = 0; i < 4; i++) begin 
      transmit(test[i]);
    end

    rx_fifo_read_i <= 1'b1;
    for (int i = 0; i < 4; i++) begin 
      case (data_width_i)
        DW_5BIT: begin 
          assert(data_rx_o == {3'b0, test[i][4:0]});
          case (parity_mode_i)
            EVEN:    assert(parity_o == (^test[i][4:0] ^ 1'b0));
            ODD:     assert(parity_o == (^test[i][4:0] ^ 1'b1));
            default: assert(parity_o == 0);
          endcase
        end

        DW_6BIT: begin 
          assert(data_rx_o == {2'b0, test[i][5:0]});
          case (parity_mode_i)
            EVEN:    assert(parity_o == (^test[i][5:0] ^ 1'b0));
            ODD:     assert(parity_o == (^test[i][5:0] ^ 1'b1));
            default: assert(parity_o == 0);
          endcase
        end

        DW_7BIT: begin 
          assert(data_rx_o == {1'b0, test[i][6:0]});
          case (parity_mode_i)
            EVEN:    assert(parity_o == (^test[i][6:0] ^ 1'b0));
            ODD:     assert(parity_o == (^test[i][6:0] ^ 1'b1));
            default: assert(parity_o == 0);
          endcase
        end

        DW_8BIT: begin 
          assert(data_rx_o == {test[i][7:0]});
          case (parity_mode_i)
            EVEN:    assert(parity_o == (^test[i][7:0] ^ 1'b0));
            ODD:     assert(parity_o == (^test[i][7:0] ^ 1'b1));
            default: assert(parity_o == 0);
          endcase
        end
      endcase
      @(posedge clk_i);
    end

    rx_fifo_read_i <= 1'b0;

    sendConfigReq();

    $finish;
  end


//---------//
//  TASKS  //
//---------//

  task reset();
    rst_n_i <= 1'b1; 
    rx_i <= RX_IDLE;
    rx_fifo_read_i <= 1'b0;
    req_ackn_i <= 1'b0;
    threshold_i <= 'b0;
    data_stream_mode <= 1'b0;
    data_width_i <= $urandom_range(3, 0);
    stop_bits_number_i <= $urandom_range(1, 0);
    parity_mode_i <= $urandom_range(3, 0);
    @(posedge clk_i);
    rst_n_i <= 1'b0; 
    @(posedge clk_i);
    rst_n_i <= 1'b1; 
  endtask : reset 


  task transmit(input logic [7:0] data);
    /* Send a start bit */
    rx_i <= !RX_IDLE;
    @(posedge clk_i);
    waitCounter();

    case (data_width_i)
      DW_5BIT: dbit_cnt = 5;
      DW_6BIT: dbit_cnt = 6;
      DW_7BIT: dbit_cnt = 7;
      DW_8BIT: dbit_cnt = 8;
    endcase

    /* Send data */
    for (int i = 0; i < dbit_cnt; i++) begin 
      rx_i <= data[i];
      waitCounter();
    end

    /* Send a parity bit */
    if (parity_mode_i == EVEN) begin 
      rx_i <= (^data) ^ 0;
      waitCounter();
    end else if (parity_mode_i == ODD) begin 
      rx_i <= (^data) ^ 1;
      waitCounter();
    end 

    case (stop_bits_number_i)
      SB_1BIT: sb_cnt = 1;
      SB_2BIT: sb_cnt = 2;
      default: sb_cnt = 1;
    endcase

    /* Send a stop bit */
    for (int i = 0; i < sb_cnt; i++) begin 
      rx_i <= RX_IDLE;
      waitCounter();
    end

    @(posedge clk_i);
  endtask : transmit


  task sendConfigReq();
    rx_i <= !RX_IDLE;
    repeat(10 * COUNT_10MS) @(posedge clk_i);
  endtask : sendConfigReq


  task waitCounter();
    while (!tick) @(posedge clk_i);
  endtask : waitCounter

endmodule : receiver_tb

module bd_counter (
  input  logic ov_baud_rt_i,
  input  logic clk_i,
  input  logic rst_n_i,
  output logic tick 
);

  logic [3:0] bd_cnt_crt, bd_cnt_nxt;

  always_ff @(posedge clk_i) begin 
    if (!rst_n_i) begin 
      bd_cnt_crt <= 4'b0;
    end else begin 
      bd_cnt_crt <= bd_cnt_nxt;
    end
  end

  always_comb begin 
    if (ov_baud_rt_i) begin 
      bd_cnt_nxt = (bd_cnt_crt == 4'd15) ? 0 : (bd_cnt_crt + 1);
      tick = (bd_cnt_crt == 4'd15);
    end else begin 
      bd_cnt_nxt = bd_cnt_crt; 
      tick = 0;
    end
  end
  
endmodule : bd_counter