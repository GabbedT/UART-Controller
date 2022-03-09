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
// FILE NAME : main_controller.sv
// DEPARTMENT : 
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// ------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : This module contains the main controller of the UART. It enables the
//               autoconfiguration of the UART once connected with another device. 
//               It receive signals from the UART's registers, FIFO's status, data
//               received and transmitter from the tx and rx module and from the 
//               baud rate generator.
//               It's resposable for error detection, data flow and settings
//               autoconfiguration.
// ------------------------------------------------------------------------------------
// KEYWORDS : ms10_counter, MS50_COUNTER, NEXT_STATE_LOGIC, ERROR_o DETECTION LOGIC
// ------------------------------------------------------------------------------------
// DEPENDENCIES : main_controller_intf.sv 
// ------------------------------------------------------------------------------------

import UART_pkg::*;

module main_controller 
( 
  input  logic         rst_n_i,
  input  logic         clk_i,
  // Data
  input  data_packet_u data_rx_i,
  input  data_packet_u data_tx_i,
  // Error detection
  input  logic         frame_error_i,
  input  logic         parity_i,
  input  logic         overrun_i,  
  input  uart_error_s  error_i,       
  // FIFO status 
  input  logic         rx_fifo_empty_i,
  input  logic         tx_fifo_empty_i,
  input  logic         rx_fifo_read_i,
  input  logic         tx_fifo_write_i,
  // Configuration
  input  logic         config_req_slv_i,
  input  logic         config_req_mst_i,
  input  logic         std_config_i,
  input  uart_config_s config_i,
  input  logic         data_stream_mode_i,
  input  logic         CFR_en_i,

  output logic         CFR_en_o,
  output uart_config_s config_o,
  output logic         config_req_mst_o,
  output logic         data_stream_mode_o,
  // FIFO operations
  output logic         rx_fifo_read_o,
  output logic         rx_fifo_write_o,
  output logic         tx_fifo_read_o,
  output logic         tx_fifo_write_o,
  // Data
  output logic         data_rx_o,
  output logic [7:0]   data_tx_o,
  // Error
  output uart_config_s error_o
);

//------------------//
// CONTROLLER LOGIC //
//------------------//

  main_control_fsm_e [NXT:CRT] state;

  logic [$clog2(COUNT_50MS) - 1:0] counter_50ms;

      // Counter to 50ms  
      always_ff @(posedge clk_i) begin : ms50_counter
        if (!rst_n_i) begin   
          counter_50ms <= 'b0;
        end else if (state[CRT] == WAIT_ACK) begin 
          counter_50ms <= counter_50ms + 1;
        end else if (counter_50ms == COUNT_50MS) begin  
          counter_50ms <= 'b0;
        end
      end : ms50_counter

  // Delay the reset signals by 1 cycle because the FSM should
  // stay 2 cycles in the IDLE stage when resetted
  logic rst_n_dly;

      always_ff @(posedge clk_i) begin : delay_register
        rst_n_dly <= rst_n_i;
      end : delay_register

      always_ff @(posedge clk_i) begin : fsm_state_register
        if (!rst_n_i) begin 
          state[CRT] <= RESET;
        end else begin 
          state[CRT] <= state[NXT];
        end
      end : fsm_state_register

  // Number of times the configuration failed
  logic [CRT:NXT][1:0] config_failed;
  
      // Count the number of times the configuration has failed (max 3 times)
      always_ff @(posedge clk_i) begin : fail_config_register
        if (!rst_n_i) begin 
          config_failed[CRT] <= 'b0;
        end else begin 
          config_failed[CRT] <= config_failed[NXT];
        end
      end : fail_config_register
      
      always_comb begin : next_state_logic 
        // Default values 
        state[NXT] = state[CRT]; 

        // Configuration signals
        CFR_en_o = CFR_en_i;
        config_o = config_i;
        config_req_mst_o = config_req_mst_i;
        data_stream_mode_o = data_stream_mode_i;

        // FIFO signals
        rx_fifo_read_o = rx_fifo_read_i;
        rx_fifo_write_o = rx_fifo_write_i;
        tx_fifo_read_o = tx_fifo_read_i;
        tx_fifo_write_o = tx_fifo_write_i;

        // Data signals
        data_rx_o = data_rx_i;
        data_tx_o = data_tx_o;

        // Error signal
        error_o = error_i; 

        case (state[CRT])

          /*
           *  Reset the device, set the configuration to the default configuration.
           */
          RESET: begin 
            CFR_en_o = 1'b1;
            config_o.data_width = STD_DATA_WIDTH; 
            config_o.parity_mode = STD_PARITY_MODE; 
            config_o.stop_bits = STD_STOP_BITS; 

            // Don't perform any operation
            config_req_mst_o = 1'b0;
            rx_fifo_read_o = 1'b0;
            rx_fifo_write_o = 1'b0;
            tx_fifo_read_o = 1'b0;
            tx_fifo_write_o = 1'b0;

            state[NXT] = MAIN;
          end

          /*  
           *  In the main state the UART is controlled by the CPU, during this state the device can 
           *  request a configuration setup or it can be requested by the other device. A standard
           *  configuration setup can also be set. 
           */
          MAIN: begin 
            // If the other device requested a configuration setup (current device = SLAVE)
            if (config_req_slv_i) begin 
              state[NXT] = SETUP_SLAVE;
            end else if (config_req_mst_i) begin 
              // If the current device request a configuration setup (current device = MASTER)
              state[NXT] = WAIT_REQ_ACKN;
            end else if (std_config_i) begin 
              state[NXT] = STD_CONFIG; 
            end 
          end

          /*
           *  The device waits for the other device to acknowledge the configuration request. 
           *  It needs to receive an acknowledge packet within 50ms otherwise the device will
           *  send another request. The process repeat for three times at the most, then the 
           *  configuration will be considered failed and the device setted up with the standard
           *  configuration.
           */
          WAIT_REQ_ACKN: begin 
            if (config_failed[CRT] == 2'd3) begin 
              error_o.configuration = 1'b1;
              config_failed[NXT] = 2'b0;
              state[NXT] = STD_CONFIG;
            end

            if (counter_50ms < COUNT_50MS) begin
              if (data_rx_i == ACKN_PKT) begin 
                state[NXT] = SETUP_MASTER;
              end
            end else begin 
              config_failed[NXT] += 'b1;
              config_req_mst_o = 1'b1;
            end
          end

          /*
           *  The device waits for configuration packets. The fifo's needs to be empty so other data packets
           *  won't be considered as configuration packets. For every packet received, the device must send
           *  an acknowledgment. If there is a configuration request from the master device, the slave must
           *  enable data stream mode so during the configuration the device doesn't interrupt everytime it 
           *  receive a packet.
           */
          SETUP_SLAVE: begin 
            CFR_en_o = 1'b1;
            data_stream_mode_o = 1'b1;

            // Wait until a configuration packet arrives, then send an acknowledge packet
            if (!tx_fifo_empty_i) begin 
              rx_fifo_read_o = 1'b1;
            end

            // If there is an error in the packet received, raise a configuration error
            // and use the standard configuration
            case (data_rx_i.id)
              END_CONFIGURATION: begin 
                CFR_en_o = 1'b0;
                state[NXT] = END_PROCESS;
              end

              DATA_WIDTH_ID: begin 
                config_o.data_width = data_rx_i.option;
                state[NXT] = SEND_ACKN;
              end

              PARITY_MODE_ID: begin  
                config_o.parity_mode = data_rx_i.option;
                state[NXT] = SEND_ACKN;
              end

              STOP_BITS_ID: begin 
                config_o.stop_bits = data_rx_i.option;
                state[NXT] = SEND_ACKN;
              end
            endcase
          end

          /*
           *  The device will send an acknowledgment packet to continue the configuration process
           */
          SEND_ACKN: begin 
            state[NXT] = SETUP_SLAVE;
            
            // Send ackowledge packet 
            tx_fifo_write_o = 1'b1;
            data_tx_o = assemble_packet(END_CONFIGURATION, 2'b00);
          end

          /*
           *  After the end configuration packet is received send the last acknowledgment packet before
           *  entering in the main state
           */
          END_PROCESS: begin 
            state[NXT] = MAIN;

            // Send ackowledge packet 
            tx_fifo_write_o = 1'b1;
            data_tx_o = ACKN_PKT;
          end

          /*
           *  The device will receive from the CPU configuration packets, during this state the data is 
           *  checked to be sure to not send any illegal packet to the slave. The illegal packet will
           *  be replaced with a packet containing the standard configuration for that field. 
           */
          SETUP_MASTER: begin 
            CFR_en_o = 1'b1;

            if (tx_fifo_write_i) begin 
              state[NXT] = WAIT_ACK;
            end

            if ((data_tx_i.id == PARITY_MODE_ID) & ((data_rx_i.option == DISABLED_1) | (data_rx_i.option == DISABLED_2))) begin 
              config_o.parity_mode = STD_PARITY_MODE;
              error_o.configuration = 1'b1;
            end else if ((data_tx_i.id == STOP_BITS_ID) & (data_rx_i.option == RESERVED)) begin 
              config_o.stop_bits = STD_STOP_BITS;
              error_o.configuration = 1'b1;
            end 
          end

          /*
           *  The device is waiting for the slave acknowledgment, the fifo must be empty. 
           *  Enable data stream mode so the device doesn't interrupt everytime it receive a packet.
           */
          WAIT_ACK: begin 
            data_stream_mode_o = 1'b1;

            if (!rx_fifo_empty_i) begin 
              rx_fifo_read_o = 1'b1;
              if (data_rx_i == ACKN_PKT) begin 
                state[NXT] = SETUP_MASTER;
              end else begin 
                state[NXT] = STD_CONFIG;
                error_o.configuration = 1'b1;
              end
            end
          end

          /*
           *  Setup the standard configuration.
           */
          STD_CONFIG: begin 
            CFR_en_o = 1'b1;
            config_o.data_width = STD_DATA_WIDTH;
            config_o.parity_mode = STD_PARITY_MODE;
            config_o.stop_bits = STD_STOP_BITS;

            state[NXT] = MAIN;
          end

        endcase
      end : next_state_logic

//-----------------------//
// ERROR DETECTION LOGIC //
//-----------------------//

  assign error_o.overrun = overrun_i;

  logic parity;

      always_comb begin : parity_detection_logic

        /*
         *  There are two types of parity checking: EVEN and ODD. Both are 
         *  computed by XORing every bit of the data, the difference 
         *  resides in the last bit XORed: 
         *  EVEN: parity ^ 0
         *  ODD:  parity ^ 1
         */
          
        case (config_i.data_width)

          DW_5BIT:  parity = ^data_rx_i[4:0];

          DW_6BIT:  parity = ^data_rx_i[5:0];

          DW_7BIT:  parity = ^data_rx_i[6:0];

          DW_8BIT:  parity = ^data_rx_i;

        endcase

        // Select ODD or EVEN parity
        case (config_i.parity_mode)

          EVEN:    error_o.parity = parity_i != (parity ^ 1'b0);

          ODD:     error_o.parity = parity_i != (parity ^ 1'b1);

          default: error_o.parity = 1'b0;
            
        endcase
      end : parity_detection_logic

  assign error_o.frame = frame_error_i;

endmodule
