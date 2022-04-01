// MIT License
//
// Copyright (c) 2021 Gabriele Tripi
// 
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
// 
// The above copyright notice and this permission notice shall be included in all
// copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.
// ------------------------------------------------------------------------------------
// ------------------------------------------------------------------------------------
// FILE NAME : transmitter.sv
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// ------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : This module contains the receiver of the uart. It is composed by
//               a main FSM and a FIFO buffer. The FSM takes care of the transaction
//               timing and interrupt assertion. When the transmitter start a 
//               configuration request the fifo keeps storing 0x00 with frame error
//               until full. Once acknowledged, the uart will go into configuration
//               process. 
//               A threshold can be set and will be useful only in data stream mode,
//               the receiver will interrupt once the fifo has receiven a certain 
//               amount of data instead of every data byte.   
// ------------------------------------------------------------------------------------
// KEYWORDS : PARAMETERS, RX FIFO, DATAPATH, FSM LOGIC, ASSERTIONS
// ------------------------------------------------------------------------------------

import UART_pkg::*;

module receiver (
  input  logic         clk_i,
  input  logic         rst_n_i,
  input  logic         ov_baud_rt_i,
  input  logic         rx_i,
  input  logic         rx_fifo_read_i,
  input  logic         req_ackn_i,
  input  logic [5:0]   threshold_i,
  input  logic         data_stream_mode,
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
  output logic         rxd_rdy_interrupt_o,
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
  localparam PARITY_BIT = 10;


//-----------//
//  RX FIFO  //
//-----------//

  /* Reset fifo if a configuration request is received */
  logic fifo_rst_n;

  /* Interface declaration, 8 data bits, 2 error bits and 1 parity bit */
  sync_fifo_interface #(11) fifo_if(clk_i);

  assign fifo_if.read_i = rx_fifo_read_i;
  assign fifo_if.rst_n_i = rst_n_i & fifo_rst_n; 

  /* FIFO buffer instantiation in FWFT mode */
  sync_FIFO_buffer #(TX_FIFO_DEPTH, 1) tx_fifo (fifo_if);

  assign rx_fifo_full_o = fifo_if.full_o;
  assign rx_fifo_empty_o = fifo_if.empty_o;


//------------//
//  DATAPATH  //
//------------//

  /* Data received */
  logic [7:0] data_rx[NXT:CRT];

      always_ff @(posedge clk_i) begin : data_register
        if (!rst_n_i) begin
          data_rx[CRT] <= 8'b0;
        end else begin 
          data_rx[CRT] <= data_rx[NXT];
        end
      end : data_register


  /* Counter to determine the amount of time the RX line 
   * stays low during configuration request */
  logic [$clog2(COUNT_10MS) - 1:0] counter_10ms[NXT:CRT];

      always_ff @(posedge clk_i) begin : ms10_counter
        if (!rst_n_i) begin 
          counter_10ms[CRT] <= 'b0;
        end else begin
          counter_10ms[CRT] <= counter_10ms[NXT];
        end
      end : ms10_counter

      always_comb begin : ms10_counter_logic
        if (rx_i != RX_IDLE) begin 
          counter_10ms[NXT] = counter_10ms[CRT] + 1'b1;
        end else if (counter_10ms[CRT] == COUNT_10MS) begin 
          counter_10ms[NXT] = 'b0;
        end else begin 
          counter_10ms[NXT] = 'b0;
        end
      end : ms10_counter_logic

  
  /* Counter for baudrate */
  logic [3:0] counter_br[NXT:CRT];

      always_ff @(posedge clk_i) begin : counter_baud_rt
        if (!rst_n_i) begin 
          counter_br[CRT] <= 4'b0;
        end else begin 
          counter_br[CRT] <= counter_br[NXT];
        end 
      end : counter_baud_rt


  /* Number of data bits received */
  logic [2:0] bits_processed[NXT:CRT]; 

      always_ff @(posedge clk_i) begin : data_bits_counter
        if (!rst_n_i) begin 
          bits_processed[CRT] <= 3'b0;
        end else begin 
          bits_processed[CRT] <= bits_processed[NXT];
        end
      end : data_bits_counter


  /* Number of stop bits received */
  logic stop_bits_cnt[NXT:CRT];

      always_ff @(posedge clk_i) begin : stop_bits_counter
        if (!rst_n_i) begin 
          stop_bits_cnt[CRT] <= 1'b0;
        end else begin 
          stop_bits_cnt[CRT] <= stop_bits_cnt[NXT];
        end
      end : stop_bits_counter

 
  logic parity_bit[NXT:CRT];
  logic stop_bits[NXT:CRT];

      always_ff @(posedge clk_i) begin 
        if (!rst_n_i) begin 
          parity_bit[CRT] <= 1'b0;
          stop_bits[CRT] <= 1'b1;
        end else begin 
          parity_bit[CRT] <= parity_bit[NXT];
          stop_bits[CRT] <= stop_bits[NXT];
        end
      end

  
  /* In data stream mode the device will interrupt if a certain
   * amount of data is received. The counter will go from 0 
   * (empty fifo) to FIFO_DEPTH - 1, if the programmer wants
   * the device to interrupt when fifo is full, then the threshold
   * must be set with the value 0. */
  logic [5:0] fifo_threshold[NXT:CRT];

      always_ff @(posedge clk_i) begin : threshold_counter
        if (!rst_n_i) begin 
          fifo_threshold[CRT] <= 'b0;
        end else begin 
          fifo_threshold[CRT] <= fifo_threshold[NXT];
        end 
      end : threshold_counter

      always_comb begin : fifo_threshold_logic
        case ({fifo_if.write_i, fifo_if.read_i})
          /* Writing */
          2'b10: fifo_threshold[NXT] =  fifo_threshold[CRT] + 1'b1;
          /* Reading */
          2'b01: fifo_threshold[NXT] =  fifo_threshold[CRT] - 1'b1;
          /* Both or no operation */
          default: fifo_threshold[NXT] =  fifo_threshold[CRT];
        endcase
      end : fifo_threshold_logic


  /* Interrupt that assert if the fifo size hit the threshold (in data stream mode)
   * or if data is received (in standard mode) */
  logic rx_rdy_int[NXT:CRT];

      always_ff @(posedge clk_i) begin : data_ready_interrupt_reg
        if (!rst_n_i) begin 
          rx_rdy_int[CRT] <= 1'b0;
        end if (!data_stream_mode & fifo_if.read_i) begin 
          /* Clear when reading data */
          rx_rdy_int[CRT] <= 1'b0;
        end else if (data_stream_mode & fifo_if.empty_o) begin 
          /* Clear only if the fifo is empty */
          rx_rdy_int[CRT] <= 1'b0;
        end else begin 
          rx_rdy_int[CRT] <= rx_rdy_int[NXT];
        end
      end : data_ready_interrupt_reg


  /* Configuration process requested. The request will be asserted
   * when the counter reaches the right value (RX low for 10ms) and
   * deasserted when the request is acknowledged */
  logic cfg_req[NXT:CRT];

      always_ff @(posedge clk_i) begin 
        if (!rst_n_i) begin 
          cfg_req[CRT] <= 1'b0;
        end else if (req_ackn_i) begin 
          cfg_req[CRT] <= 1'b0;
        end else begin 
          cfg_req[CRT] <= cfg_req[NXT];
        end
      end

  assign config_req_slv_o = cfg_req[CRT];


//-------------//
//  FSM LOGIC  //
//-------------//

  typedef enum logic [2:0] {
    /* The device is waiting for data */
    IDLE,
    /* Sample start bit */
    START,
    /* Sample the data bits*/
    SAMPLE,
    /* Sample parity bit */
    PARITY,
    /* Sample stop bits to end the transaction */
    DONE
  } receiver_fsm_e;


  /* FSM current and next state */
  receiver_fsm_e state[NXT:CRT];

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
        cfg_req[NXT] = cfg_req[CRT];
        stop_bits[NXT] = stop_bits[CRT];
        parity_bit[NXT] = parity_bit[CRT];
        counter_br[NXT] = counter_br[CRT];
        rx_rdy_int[NXT] = rx_rdy_int[CRT];
        stop_bits_cnt[NXT] = stop_bits_cnt[CRT];
        bits_processed[NXT] = bits_processed[CRT];

        rx_done_o = 1'b0;
        fifo_if.write_i = 1'b0;
        fifo_rst_n = 1'b1;

        if (counter_10ms[CRT] == COUNT_10MS) begin 
          cfg_req[NXT] = 1'b1;
          state[NXT] = IDLE;
          /* Reset fifo only if the request is acknowledged */
          fifo_rst_n = !req_ackn_i;
        end 

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

                if (parity_mode_i[1]) begin
                  case (data_width_i) 
                    DW_5BIT: state[NXT] = (bits_processed[CRT] == 4'd4) ? DONE : SAMPLE;
                    DW_6BIT: state[NXT] = (bits_processed[CRT] == 4'd5) ? DONE : SAMPLE;
                    DW_7BIT: state[NXT] = (bits_processed[CRT] == 4'd6) ? DONE : SAMPLE;
                    DW_8BIT: state[NXT] = (bits_processed[CRT] == 4'd7) ? DONE : SAMPLE;
                  endcase
                end else begin 
                  case (data_width_i) 
                    DW_5BIT: state[NXT] = (bits_processed[CRT] == 4'd4) ? PARITY : SAMPLE;
                    DW_6BIT: state[NXT] = (bits_processed[CRT] == 4'd5) ? PARITY : SAMPLE;
                    DW_7BIT: state[NXT] = (bits_processed[CRT] == 4'd6) ? PARITY : SAMPLE;
                    DW_8BIT: state[NXT] = (bits_processed[CRT] == 4'd7) ? PARITY : SAMPLE;
                  endcase
                end
              end
            end else begin 
              counter_br[NXT] = counter_br[CRT] + 1'b1;
            end
          end

          /* 
           *  Sample parity bit. 
           */
          PARITY: begin 
            if (ov_baud_rt_i) begin 
              if (counter_br[CRT] == 4'd15) begin 
                counter_br[NXT] = 4'b0;
                parity_bit[NXT] = rx_i;
                state[NXT] = DONE;
              end
            end
          end

          /* 
           *  During DONE state, the stop bits are detected. During 
           *  this time the RX line must be stable on IDLE.
           */
          DONE: begin  
            /* Raise an interrupt */
            if (data_stream_mode & (threshold_i != 'b0)) begin 
              /* Interrupt if fifo size is greater or equal the threshold value */
              rx_rdy_int[NXT] = (fifo_threshold[CRT] >= threshold_i);
            end else if (data_stream_mode & (threshold_i == 'b0)) begin 
              /* Interrupt only if fifo is full */
              rx_rdy_int[NXT] = fifo_if.full_o;    
            end else begin
              rx_rdy_int[NXT] = 1'b1;
            end


            if (ov_baud_rt_i) begin
              if (counter_br[CRT] == 4'd15) begin
                /* AND the rx line with the stop bits so if in the
                 * previous cycle the stop bits wasn't detected 
                 * (logic 0) then the information doesn't get lost */
                stop_bits[NXT] = stop_bits[CRT] & rx_i;

                case (stop_bits_number_i)
                  SB_1BIT: begin 
                    state[NXT] = IDLE; 
                    fifo_if.write_i = 1'b1 & !fifo_if.full_o;
                    rx_done_o = 1'b1;
                  end

                  SB_2BIT: begin 
                    stop_bits_cnt[NXT] = 1'b1;
                    state[NXT] = (stop_bits_cnt[CRT]) ? IDLE : DONE; 
                    fifo_if.write_i = stop_bits_cnt[CRT] & !fifo_if.full_o;
                    rx_done_o = stop_bits_cnt[CRT];
                  end
                  
                  default: begin 
                    state[NXT] = IDLE; 
                    fifo_if.write_i = 1'b1 & !fifo_if.full_o;
                    rx_done_o = 1'b1;
                  end
                endcase
              end
            end
          end
        endcase
      end


      always_comb begin : fifo_write_data_assignment
        fifo_if.wr_data_i[7:0] = data_rx[CRT];
 
        case (parity_mode_i)
          EVEN:    fifo_if.wr_data_i[PARITY_BIT] = parity_bit[CRT] ^ 1'b0;
          ODD:     fifo_if.wr_data_i[PARITY_BIT] = parity_bit[CRT] ^ 1'b1;
          default: fifo_if.wr_data_i[PARITY_BIT] = 1'b0;
        endcase

        /* AND the stop bits with the RX line: if the first stop bits was 0
         * then 'stop_bits[CRT]' would be 0 too generating a frame error. 
         * The same goes for the single stop bit. If uart is receiving 0x00
         * then frame error is disabled */
        fifo_if.wr_data_i[FRAME] = (data_rx[CRT] == 8'b0) ? 1'b0 : !(stop_bits[CRT] & rx_i);

        /* Raise an overrun error if the fifo has reached the threshold level or
         * the data has been received and the device is receiving other data */
        fifo_if.wr_data_i[OVERRUN] = rx_rdy_int[CRT] & (state[CRT] != IDLE);
      end : fifo_write_data_assignment

  /* Output assignment */
  assign data_rx_o = fifo_if.rd_data_o[7:0];
  assign frame_error_o = fifo_if.rd_data_o[FRAME];
  assign overrun_error_o = fifo_if.rd_data_o[OVERRUN];
  assign parity_o = fifo_if.rd_data_o[PARITY_BIT];
  assign rxd_rdy_interrupt_o = rx_rdy_int[CRT];


//--------------//
//  ASSERTIONS  //
//--------------//

  /* Reset FSM state with an acknowledge */
  property req_ackn_state_chk;
    @(posedge clk_i) ((counter_10ms[CRT] == COUNT_10MS) && req_ackn_i) |=> (state[CRT] == IDLE);
  endproperty

  /* While not in data stream mode, the interrupt must be asserted while receiving the stop bits */
  property interrupt_raise_chk;
    @(posedge clk_i) (!data_stream_mode && (state[CRT] == DONE)) |=> rxd_rdy_interrupt_o;
  endproperty

  /* The interrupt should be asserted till it's cleared with a read */
  property interrupt_clear_chk;
    @(posedge clk_i) $rose(rxd_rdy_interrupt_o) && !data_stream_mode |=> (rxd_rdy_interrupt_o throughout rx_fifo_read_i [->1]) ##1 !rxd_rdy_interrupt_o;
  endproperty

  /* Check frame error detection */
  property frame_error_chk;
    @(posedge clk_i) (!rx_i && (state[CRT] == DONE)) |-> !fifo_if.wr_data_i[FRAME];
  endproperty

  /* Check threshold logic */
  property threshold_empty_chk;
    @(posedge clk_i) (threshold_counter[CRT] == 0) |-> fifo_if.empty_o;
  endproperty

  property threshold_full_chk;
    @(posedge clk_i) (threshold_counter[CRT] == (RX_FIFO_DEPTH - 1)) |-> fifo_if.full_o;
  endproperty


endmodule : receiver