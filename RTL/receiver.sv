import UART_pkg::*;

module receiver (
  input  logic         clk_i,
  input  logic         rst_n_i,
  input  logic         ov_baud_rt_i,
  input  logic         rx_i,
  input  logic         rx_fifo_read_i,
  input  logic [1:0]   data_width_i,
  input  logic [1:0]   stop_bits_number_i,
  input  logic [1:0]   parity_mode_i,

  output logic         rx_fifo_full_o,
  output logic         rx_fifo_empty_o,
  output logic         config_req_slv_o,
  output logic         overrun_error_o,
  output logic         frame_error_o,
  output logic         parity_o,
  output logic         rx_done_o,
  output logic [7:0]   data_rx_o
);

//--------------//
//  PARAMETERS  //
//--------------//

  /* How many clock cycles does it need to reach 10 ms */ 
  /* based on a specific system clock */
  localparam COUNT_10MS = SYSTEM_CLOCK_FREQ / 100;

  /* Next and current state */
  localparam NXT = 1;
  localparam CRT = 0;

  /* TX line in idle state */
  localparam RX_IDLE = 1;

  /* TX line start */
  localparam RX_START = 0;

  /* Index in fifo data */
  localparam FRAME = 8;
  localparam OVERRUN = 9;
  localparam PARITY = 10;


//-----------//
//  RX FIFO  //
//-----------//

  /* Interface declaration, 8 data bits, 2 error bits and 1 parity bit */
  sync_fifo_interface #(11) fifo_if(clk_i);

  assign fifo_if.read_i = rx_fifo_read_i;
  assign fifo_if.rst_n_i = rst_n_i; 

  /* Output assignment */
  assign data_rx_o = fifo_if.rd_data_o[7:0];
  assign frame_error_o = fifo_if.rd_data_o[FRAME];
  assign overrun_error_o = fifo_if.rd_data_o[OVERRUN];
  assign parity_o = fifo_if.rd_data_o[PARITY];

  /* FIFO buffer instantiation in FWFT mode */
  sync_FIFO_buffer #(TX_FIFO_DEPTH, 1) tx_fifo (fifo_if);

  assign rx_fifo_full_o = fifo_if.full_o;
  assign rx_fifo_empty_o = fifo_if.empty_o;


//------------//
//  DATAPATH  //
//------------//

  /* Data received */
  logic [NXT:CRT][7:0] data_rx;

  assign fifo_if.wr_data_i[7:0] = data_rx[CRT];

      /* Register the output to not lose data */
      always_ff @(posedge clk_i) begin : data_register
        if (!rst_n_i) begin
          data_rx[CRT] <= 8'b0;
        end else begin 
          data_rx[CRT] <= data_rx[NXT];
        end
      end : data_register


  logic [NXT:CRT][$clog2(COUNT_10MS) - 1:0] counter_10ms;

      /* Counter to determine the amount of time the RX line 
       * stays low during configuration request */
      always_ff @(posedge clk_i) begin : ms10_counter
        if (!rst_n_i) begin 
          counter_10ms[CRT] <= 'b0;
        end else begin
          counter_10ms[CRT] <= counter_10ms[NXT];
        end
      end : ms10_counter

  
  /* Counter for baudrate */
  logic [NXT:CRT][3:0] counter_br;

      always_ff @(posedge clk_i) begin : counter_baud_rt
        if (!rst_n_i) begin 
          counter_br[CRT] <= 4'b0;
        end else begin 
          counter_br[CRT] <= counter_br[NXT];
        end 
      end : counter_baud_rt


  /* Number of data bits received */
  logic [NXT:CRT][2:0] bits_processed; 

      always_ff @(posedge clk_i) begin : data_bits_counter
        if (!rst_n_i) begin 
          bits_processed[CRT] <= 3'b0;
        end else begin 
          bits_processed[CRT] <= bits_processed[NXT];
        end
      end : data_bits_counter


  /* Number of stop bits received */
  logic [NXT:CRT] stop_bits_cnt;

      always_ff @(posedge clk_i) begin : stop_bits_counter
        if (!rst_n_i) begin 
          stop_bits_cnt[CRT] <= 1'b0;
        end else begin 
          stop_bits_cnt[CRT] <= stop_bits_cnt[NXT];
        end
      end : stop_bits_counter

  
  logic [NXT:CRT] parity_bit;
  logic [NXT:CRT] stop_bits;

      always_ff @(posedge clk_i) begin 
        if (!rst_n_i) begin 
          parity_bit[CRT] <= 1'b0;
          stop_bits[CRT] <= 1'b1;
        end else begin 
          parity_bit[CRT] <= parity_bit[NXT];
          stop_bits[CRT] <= stop_bits[NXT];
        end
      end


//-------------//
//  FSM LOGIC  //
//-------------//

  typedef enum logic [2:0] {
    /* The device is waiting for data */
    IDLE,
    /* A configuration is being requested */
    CFG_REQ,
    /* Sample start bit */
    START,
    /* Sample the data bits*/
    SAMPLE,
    /* Sample stop bits to end the transaction */
    DONE
  } receiver_fsm_e;


  /* FSM current and next state */
  transmitter_fsm_e [NXT:CRT] state;

      always_ff @(posedge clk_i) begin : fsm_state_register
        if (!rst_n_i) begin 
          state[CRT] <= IDLE;
        end else begin 
          state[CRT] <= state[NXT];
        end
      end : fsm_state_register


      always_comb begin 

        //------------------//
        //  DEFAULT VALUES  //
        //------------------//

        state[NXT] = state[CRT];
        data_rx[NXT] = data_rx[CRT];
        stop_bits[NXT] = stop_bits[CRT];
        stop_bits_cnt[NXT] = stop_bits_cnt[CRT];
        parity_bit[NXT] = parity_bit[CRT];
        counter_br[NXT] = counter_br[CRT];
        bits_processed[NXT] = bits_processed[CRT];

        config_req_slv_o = 1'b0;
        rx_done_o = 1'b0;
        fifo_if.write_i = 1'b0;

        if (rx_i != RX_IDLE) begin 
          counter_10ms[NXT] = counter_10ms[CRT] + 1'b1;
        end else begin 
          counter_10ms[NXT] = 'b0;
        end
        
        /* FIFO data assignment */
        case (parity_mode_i)
          EVEN:    fifo_if.wr_data_i[PARITY] = parity_bit[CRT] ^ 1'b0;
          ODD:     fifo_if.wr_data_i[PARITY] = parity_bit[CRT] ^ 1'b1;
          default: fifo_if.wr_data_i[PARITY] = 1'b0;
        endcase

        /* AND the stop bits with the RX line: if the first stop bits was 0
         * then 'stop_bits[CRT]' would be 0 too generating a frame error. 
         * The same goes for the single stop bit */
        fifo_if.wr_data_i[FRAME] = !(stop_bits[CRT] & rx_i);
        fifo_if.wr_data_i[OVERRUN] = fifo_if.full_o;

        case (state[CRT])

          /* 
           *  The device is waiting for data to arrives.
           */
          IDLE: begin 
            if (rx_i != RX_IDLE) begin 
              counter_br[NXT] = 4'b0;
              state[NXT] = START;
            end
          end

          /* 
           *  Sample the start bit in T/2 time (T is the bit while the
           *  bit is stable) to grant maximum signal stability.
           */
          START: begin 
            if (ov_baud_rt_i) begin 
              /* Reach the middle of the bit */
              if (counter_br[CRT] == 4'd7) begin 
                bits_processed[NXT] = 3'b0;
                counter_br[NXT] = 4'b0;
                state[NXT] = SAMPLE;
              end else begin 
                counter_br[NXT] = counter_br[CRT] + 1'b1;
              end
            end
          end

          /* 
           *  Sample data bits. Since in the START state the counter stopped
           *  at half of the bit and then switched state, now every time the
           *  counter reach T, it is in the middle of the start bit. The LSB
           *  is received first.
           */
          SAMPLE: begin 
            /* Reset stop bits */
            stop_bits[NXT] = 1'b1;

            if (ov_baud_rt_i) begin 
              if (counter_br[CRT] == 4'd15) begin 
                counter_br[NXT] = 4'b0;
                bits_processed[NXT] = bits_processed[CRT] + 1'b1;

                /* Place the bit in the MSB of the data register,
                 * in the next clock cycle it will be shifted to 
                 * the right */
                data_rx[NXT] = {rx_i, data_rx[CRT][7:1]};

                case (data_width_i) 
                  DW_5BIT: begin
                    state[NXT] = (bits_processed[CRT] == 4'd4) ? DONE : DATA;
                    parity_bit[NXT] = ^data_rx[NXT][4:0];
                  end

                  DW_6BIT: begin 
                    state[NXT] = (bits_processed[CRT] == 4'd5) ? DONE : DATA;
                    parity_bit[NXT] = ^data_rx[NXT][5:0];
                  end

                  DW_7BIT: begin 
                    state[NXT] = (bits_processed[CRT] == 4'd6) ? DONE : DATA;
                    parity_bit[NXT] = ^data_rx[NXT][6:0];
                  end

                  DW_8BIT: begin 
                    state[NXT] = (bits_processed[CRT] == 4'd7) ? DONE : DATA;
                    parity_bit[NXT] = ^data_rx[NXT];
                  end
                endcase
              end
            end else begin 
              counter_br[NXT] = counter_br[CRT] + 1'b1;
            end
          end

          /* 
           *  During DONE state, the stop bits are detected. During 
           *  this time the RX line must be stable on IDLE.
           */
          DONE: begin  
            if (ov_baud_rt_i) begin
              if (counter_br[CRT] == 4'd15) begin
                /* AND the rx line with the stop bits so if in the
                 * previous cycle the stop bits wasn't detected 
                 * (logic 0) then the information doesn't get lost */
                stop_bits[NXT] = stop_bits[CRT] & rx_i;

                case (stop_bits_number_i)
                  SB_1BIT: begin 
                    state[NXT] = IDLE; 
                    fifo_if.write_i = 1'b1;
                    rx_done_o = 1'b1;
                  end

                  SB_2BIT: begin 
                    stop_bits_cnt[NXT] = 1'b1;
                    state[NXT] = (stop_bits_cnt[CRT]) ? IDLE : DONE; 
                    fifo_if.write_i = stop_bits_cnt[CRT];
                    rx_done_o = stop_bits_cnt[CRT];
                  end
                  default:
                endcase
              end
            end
          end

        endcase
      end

endmodule : receiver