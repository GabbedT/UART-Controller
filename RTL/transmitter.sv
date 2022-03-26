import UART_pkg::*;

module transmitter (
  input  logic         clk_i,
  input  logic         rst_n_i,
  input  logic         ov_baud_rt_i,
  input  logic [7:0]   data_tx_i,
  input  logic         tx_fifo_write_i,
  input  logic         config_req_mst_i,
  input  logic [1:0]   data_width_i,
  input  logic [1:0]   stop_bits_number_i,

  output logic         tx_o,
  output logic         tx_done_o,      
  output logic         req_done_o,
  output logic         tx_fifo_empty_o,
  output logic         tx_fifo_full_o
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
  localparam TX_IDLE = 1;

  /* TX line start */
  localparam TX_START = 0;

  
//-----------//
//  TX FIFO  //
//-----------//

  /* Interface declaration */
  sync_fifo_interface #(8) fifo_if(clk_i);

  /* Read a word from FIFO */
  logic read_fifo;

  assign fifo_if.wr_data_i = data_tx_i;
  assign fifo_if.read_i = read_fifo;
  assign fifo_if.write_i = tx_fifo_write_i;
  assign fifo_if.rst_n_i = rst_n_i; 

  /* FIFO buffer instantiation in FWFT mode */
  sync_FIFO_buffer #(TX_FIFO_DEPTH, 1) tx_fifo (fifo_if);

  assign tx_fifo_full_o = fifo_if.full_o;
  assign tx_fifo_empty_o = fifo_if.empty_o;


//------------//
//  DATAPATH  //
//------------//

  /* Data to be transmitted */
  logic [NXT:CRT][7:0] data_tx;

      /* Register the output to not lose data */
      always_ff @(posedge clk_i) begin : data_register
        if (!rst_n_i) begin
          data_tx[CRT] <= 8'b0;
        end else if (!fifo_if.empty_o) begin 
          data_tx[CRT] <= data_tx[NXT];
        end
      end : data_register


  logic [NXT:CRT][$clog2(COUNT_10MS) - 1:0] counter_10ms;

      /* Counter to determine the amount of time the TX line 
       * must stay low during configuration request */
      always_ff @(posedge clk_i) begin : ms10_counter
        if (!rst_n_i) begin 
          counter_10ms[CRT] <= 'b0;
        end else begin
          counter_10ms[CRT] <= counter_10ms[NXT];
        end
      end : ms10_counter

  
  /* Drive the TX line */
  logic tx_line;

      always_ff @(posedge clk_i) begin : tx_line_register 
        if (!rst_n_i) begin 
          tx_o <= TX_IDLE;
        end else begin
          tx_o <= tx_line;
        end
      end : tx_line_register

  
  /* Counter for baudrate */
  logic [NXT:CRT][3:0] counter_br;

      always_ff @(posedge clk_i) begin : counter_baud_rt
        if (!rst_n_i) begin 
          counter_br[CRT] <= 4'b0;
        end else begin 
          counter_br[CRT] <= counter_br[NXT];
        end 
      end : counter_baud_rt


  /* Number of data bits sended */
  logic [NXT:CRT][2:0] bits_processed; 

      always_ff @(posedge clk_i) begin : data_bits_counter
        if (!rst_n_i) begin 
          bits_processed[CRT] <= 3'b0;
        end else begin 
          bits_processed[CRT] <= bits_processed[NXT];
        end
      end : data_bits_counter

  
  /* Number of stop bits sended */
  logic [NXT:CRT] stop_bits;

      always_ff @(posedge clk_i) begin : stop_bits_counter
        if (!rst_n_i) begin 
          stop_bits[CRT] <= 1'b0;
        end else begin 
          stop_bits[CRT] <= stop_bits[NXT];
        end
      end : stop_bits_counter

  
//-------------//
//  FSM LOGIC  //
//-------------//

  typedef enum logic [2:0] {
    /* The device is waiting for data */
    IDLE,
    /* Send a configuration request */
    CFG_REQ,
    /* Inform the other device that data is arriving
     * by sending a start bit */
    START,
    /* Transmit the data bits serially to the other device*/
    DATA,
    /* Send stop bits to end the transaction */
    DONE
  } transmitter_fsm_e;

  /* FSM current and next state */
  transmitter_fsm_e [NXT:CRT] state;

      always_ff @(posedge clk_i) begin : fsm_state_register
        if (!rst_n_i) begin 
          state[CRT] <= IDLE;
        end else begin 
          state[CRT] <= state[NXT];
        end
      end : fsm_state_register


      always_comb begin : fsm_next_state_logic

        //------------------//
        //  DEFAULT VALUES  //
        //------------------//

        state[NXT] = state[CRT];
        data_tx[NXT] = data_tx[CRT];
        stop_bits[NXT] = stop_bits[CRT];
        counter_br[NXT] = counter_br[CRT];
        counter_10ms[NXT] = counter_10ms[CRT];
        bits_processed[NXT] = bits_processed[CRT];

        tx_line = TX_IDLE;
        tx_done_o = 1'b0;
        read_fifo = 1'b0;
        req_done_o = 1'b0;

        case(state[CRT])

          /* 
           *  The device is simply waiting for data to transmit. If there 
           *  is a configuration request and FIFO is not empty, clear the 
           *  buffer by transmitting all the data, then send the request.
           */
          IDLE: begin 
            if (!fifo_if.empty_o) begin 
              state[NXT] = START;
            end else if (config_req_mst_i) begin 
              state[NXT] = CFG_REQ;
            end
          end

          /* 
           *  Set tx line to logic 0 for 10ms.  
           */
          CFG_REQ: begin 
            counter_10ms[NXT] = counter_10ms[CRT] + 1'b1;
            tx_line = !TX_IDLE;

            if (counter_10ms[CRT] == COUNT_10MS) begin 
              req_done_o = 1'b1;
              state[NXT] = IDLE;
              counter_10ms[NXT] = 'b0;
            end
          end

          /* 
           *  Send start bit the the receiver device and load the data
           *  register with the data to be transmitted.
           */
          START: begin 
            tx_line = TX_START;

            if (ov_baud_rt_i) begin 
              if (counter_br[CRT] == 4'd15) begin 
                state[NXT] = DATA;
                counter_br[NXT] = 4'b0;
                read_fifo = 1'b1;
                data_tx[NXT] = fifo_if.rd_data_o;                
              end else begin 
                counter_br[NXT] = counter_br[CRT] + 1'b1;
              end
            end
          end

          /* 
           *  Send data bits serially, every 16 tick process the next bit of data.
           */
          DATA: begin 
            tx_line = data_tx[CRT][0];

            if (ov_baud_rt_i) begin 
              if (counter_br[CRT] == 4'd15) begin 
                /* Shift the data to send the next bit and increment
                 * the bit counter */
                data_tx[NXT] = data_tx[CRT] >> 1'b1;
                bits_processed[NXT] = bits_processed[CRT] + 1'b1;
                counter_br[NXT] = 4'b0;

                /* Send a fixed amount of bits based on configuration parameter */
                case (data_width_i)  
                  DW_5BIT:  state[NXT] = (bits_processed[CRT] == 4'd4) ? DONE : DATA;
                  DW_6BIT:  state[NXT] = (bits_processed[CRT] == 4'd5) ? DONE : DATA;
                  DW_7BIT:  state[NXT] = (bits_processed[CRT] == 4'd6) ? DONE : DATA;
                  DW_8BIT:  state[NXT] = (bits_processed[CRT] == 4'd7) ? DONE : DATA;
                endcase
              end else begin 
                counter_br[NXT] = counter_br[CRT] + 1'b1;
              end
            end
          end

          /* 
           *  Send stop bits to end the transaction.
           */
          DONE: begin 
            tx_line = TX_IDLE;

            if (ov_baud_rt_i) begin 
              if (counter_br[CRT] == 4'd15) begin 
                case (stop_bits_number_i)
                  SB_1BIT: begin 
                    state[NXT] = IDLE;
                    tx_done_o = 1'b1;
                  end

                  SB_2BIT: begin 
                    state[NXT] = (stop_bits[CRT]) ? IDLE : DONE;
                    tx_done_o = stop_bits[CRT];
                    stop_bits[NXT] = 1'b1;
                  end

                  default: begin 
                    state[NXT] = IDLE;
                    tx_done_o = 1'b1;
                  end
                endcase

                counter_br[NXT] = 4'b0;
              end else begin 
                counter_br[NXT] = counter_br[CRT] + 1'b1;
              end
            end
          end

        endcase

      end : fsm_next_state_logic


//--------------//
//  ASSERTIONS  //
//--------------//

/* After the device is done transmitting, lower the request signal */
property req_done_chk;
  @(posedge clk_i) req_done_o |=> !config_req_mst_i;
endproperty

/* While sending the request, the tx line must be stable for 10ms */
property tx_stable_chk;
  @(posedge clk_i) ((fifo_if.empty_o) && (state[CRT] == CFG_REQ)) |-> (!tx_o[*COUNT_10MS]);
endproperty

/* Send two stop bits. Tx should be high for 2 clock cycles */
property two_stop_bits_chk;
  @(posedge clk_i) ((state[CRT] == DONE) && (stop_bits_number_i == SB_2BIT)) |=> (tx_o[*2]); 
endproperty

/* The FIFO must not be written if it's full */
property full_chk;
  @(posedge clk_i) fifo_if.full_o |-> !tx_fifo_write_i;
endproperty

/* Read FIFO only in start state */
property read_chk;
  @(posedge clk_i) (state[CRT] != START) |-> !fifo_if.read_i;
endproperty

  initial begin 
    
    assert property (req_done_chk)
    else $display("Request done, the request signal wasn't deassert!");

    assert property (tx_stable_chk)
    else $display("Tx line not stable on low");

    assert property (two_stop_bits_chk)
    else $display("Error on sending 2 stop bits, tx line must be stable on high for 2 clock cycles");

    assert property (full_chk)
    else $display("Writing on full FIFO, data lost!");

    assert property (read_chk)
    else $display("Reading fifo while not sending start bits, data lost!");

  end

endmodule : transmitter
