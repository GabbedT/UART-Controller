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
// KEYWORDS : ms10_counter, MS50_COUNTER, NEXT_STATE_LOGIC, ERROR DETECTION LOGIC
// ------------------------------------------------------------------------------------
// DEPENDENCIES : main_controller_intf.sv 
// ------------------------------------------------------------------------------------

`include "main_controller_intf.sv"
import UART_pkg::*;

module main_controller ( main_controller_intf if_ );

//------------------//
// CONTROLLER LOGIC //
//------------------//

  main_control_fsm_e [NXT:CRT] state;

  logic [$clog2(COUNT_10MS) - 1:0] counter_10ms;
  logic [$clog2(COUNT_50MS) - 1:0] counter_50ms;

      // Counter to 10ms
      always_ff @(posedge if_.clk_i) begin : ms10_counter
        if (!if_.rst_n_i) begin 
          counter_10ms <= 'b0;
        end else if (!if_.rx_i) begin 
          counter_10ms <= counter_10ms + 1;
        end else if (if_.rx_i) begin
          counter_10ms <= 'b0;
        end else if (counter_10ms == COUNT_10MS) begin 
          counter_10ms <= 'b0;
        end
      end : ms10_counter

      // Counter to 50ms
      always_ff @(posedge if_.clk_i) begin : ms50_counter
        if (!if_.rst_n_i) begin   
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

      always_ff @(posedge if_.clk_i) begin
        rst_n_dly <= if_.rst_n_i;
      end

      always_ff @(posedge if_.clk_i) begin : fsm_state_register
        if (!if_.rst_n_i) begin 
          state[CRT] <= RESET;
        end else begin 
          state[CRT] <= state[NXT];
        end
      end : fsm_state_register

  // Number of times the configuration failed
  logic [CRT:NXT][1:0] config_failed;

      // Count the number of times the configuration has failed (max 3 times)
      always_ff @(posedge if_.clk_i) begin : fail_config_register
        if (!if_.rst_n_i) begin 
          config_failed[CRT] <= 'b0;
        end else begin 
          config_failed[CRT] <= config_failed[NXT];
        end
      end : fail_config_register
      
      always_comb begin : next_state_logic 
        // Default values 
        // Configuration signals
        if_.config_en_o = if_.config_en_i;
        if_.config_o.data_width = if_.config_i.data_width;
        if_.config_o.stop_bits = if_.config_i.stop_bits;
        if_.config_o.parity_mode = if_.config_i.parity_mode;
        if_.error_o.configuration = 1'b0;
        config_failed[NXT] = config_failed[CRT];

        // FIFO signals
        if_.tx_fifo_write_o = if_.tx_fifo_write_i;
        if_.rx_fifo_read_o = if_.rx_fifo_read_i;
        if_.rx_fifo_write_o = 1'b1;
        if_.tx_fifo_read_o = 1'b1;

        // Data signals 
        if_.data_tx_o = if_.data_tx_i;
        if_.drive_tx_o = TRANSMITTER;
        if_.tx_o = IDLE;

        // FSM state
        state[NXT] = state[CRT]; 

        case (state[CRT])

          RESET:  begin       
                    if (if_.autoconfig_en_i) begin 
                      state[NXT] = (if_.device_type_i == MASTER) ? SETUP : ACKN;
                    end else begin 
                      state[NXT] = MAIN;
                    end

                    // Standard configuration
                    if_.config_o.data_width = STD_DATA_WIDTH;
                    if_.config_o.stop_bits = STD_STOP_BITS;
                    if_.config_o.parity_mode = STD_PARITY_MODE;

                    // Don't enable writing and reading
                    if_.tx_fifo_write_o = 1'b0;
                    if_.rx_fifo_read_o = 1'b0;
                    if_.rx_fifo_write_o = 1'b0;
                    if_.tx_fifo_read_o = 1'b0;
                  end

          // If the device is the slave then it expects to see the RX line low (not IDLE).
          // In that case send an acknowledgment packet (the counter starts only if the 
          // RX line is not IDLE)
          ACKN: begin
                  if (counter_10ms == COUNT_10MS) begin  
                    state[NXT] = MAIN;

                    // Send 0xFF to acknowledge the connection
                    if_.tx_fifo_write_o = 1'b1;
                    if_.data_tx_o = 8'hFF;
                  end else begin 
                    state[NXT] = ACKN;

                    // Don't send anything 
                    if_.tx_fifo_write_o = 1'b0;
                    if_.data_tx_o = 8'hFF;
                  end
                end
            
          // Drive the TX line low (not IDLE) to inform the other device (SLAVE) that the MASTER
          // is ready for configuration
          SETUP:  begin 
                    // Drive TX line to 0 and wait 10ns 
                    if_.tx_o = 1'b0; 
                    if_.drive_tx_o = CONTROLLER; 
                    state[NXT] = (counter_10ms == COUNT_10MS) ? WAIT_ACK : state[CRT];
                  end

          // Wait for the slave's acknowledge signal. If it fails repeat the SETUP and WAIT states for two more times
          WAIT_ACK: begin 
                      // Set TX line to idle
                      if_.tx_o = IDLE;
                      if_.drive_tx_o = CONTROLLER;

                      // Read the FIFO only when a packet has been sended (once the baud rate tick)
                      if_.rx_fifo_read_o = if_.baud_rt_tick_i & !if_.tx_fifo_empty_i;

                      // If the timer reach 50ms and the packet received is 0xFF then go in configuration mode
                      if ((counter_50ms == COUNT_50MS) & (if_.data_rx_i == 8'hFF)) begin : valid_packet
                        state[NXT] = DATA_WD;
                      end else if ((counter_50ms == COUNT_50MS) & (if_.data_rx_i != 8'hFF)) begin : invalid_packet
                        // If the packet received is not valid try another time 
                        state[NXT] = SETUP;
                        config_failed[NXT] = config_failed[CRT] + 1;
                      end else if (config_failed[CRT] == 2'd3) begin : failed_configuration
                        // If it fails 3 times then go in standard configuration
                        state[NXT] = STD_CONFIG;
                      end else begin : wait_counter
                        // Wait for the counter to reach 50ms
                        state[NXT] = WAIT_ACK;
                      end
                    end
            
          // Configure UART's data width packet
          DATA_WD:  begin 
                      // Read the FIFO only when a packet has been sended (once the baud rate tick)
                      if_.rx_fifo_read_o = if_.baud_rt_tick_i & !if_.tx_fifo_empty_i;

                      // If there is a match, enable the configuration
                      if (if_.data_rx_i.cfg_packet.id == DATA_WIDTH_ID) begin : data_width_id_match
                        if_.config_o.data_width = if_.data_rx_i.cfg_packet.option;
                        if_.config_en_o = 1'b1;
                        if_.error_o.configuration = 1'b0;

                        // Send an acknowledge packet and go to the next state
                        if_.tx_fifo_write_o = 1'b1;
                        if_.data_tx_o = 8'hFF;
                        state[NXT] = STOP_BT;
                      end else begin : data_width_id_mismatch
                        // Block it and raise a configuration error
                        if_.config_o.data_width = if_.config_i.data_width;
                        if_.config_en_o = 1'b0;
                        if_.error_o.configuration = 1'b1;
                      end
                    end

          // Configure UART's number of stop bits
          STOP_BT:  begin 
                      // Read the FIFO only when a packet has been sended (once the baud rate tick)
                      if_.rx_fifo_read_o = if_.baud_rt_tick_i & !if_.tx_fifo_empty_i;

                      // If there is a match enable the configuration
                      if (if_.data_rx_i.cfg_packet.id == STOP_BITS_ID) begin : stop_bits_id_match
                        if_.config_o.stop_bits = if_.data_rx_i.cfg_packet.option;
                        if_.config_en_o = 1'b1;
                        if_.error_o.configuration = 1'b0;

                        // Send an acknowledge packet and go to the next state
                        if_.tx_fifo_write_o = 1'b1;
                        if_.data_tx_o = 8'hFF;
                        state[NXT] = PARITY;
                      end else begin : stop_bits_id_mismatch
                        // Block it and raise a configuration error
                        if_.config_o.stop_bits = if_.config_i.stop_bits;
                        if_.config_en_o = 1'b0;
                        if_.error_o.configuration = 1'b1;
                      end
                    end

          // Configure UART's number of stop bits
          PARITY: begin 
                    // Read the FIFO only when a packet has been sended (once the baud rate tick)
                    if_.rx_fifo_read_o = if_.baud_rt_tick_i & !if_.tx_fifo_empty_i;

                    // If there is a match enable the configuration
                    if (if_.data_rx_i.cfg_packet.id == PARITY_MODE_ID) begin : parity_mode_id_match
                      if_.config_o.stop_bits = if_.data_rx_i.cfg_packet.option;
                      if_.config_en_o = 1'b1;
                      if_.error_o.configuration = 1'b0;

                      // Send an acknowledge packet and go to the next state
                      if_.tx_fifo_write_o = 1'b1;
                      if_.data_tx_o = 8'hFF;
                      state[NXT] = MAIN;
                    end else begin : parity_mode_id_mismatch
                      // Block it and raise a configuration error
                      if_.config_o.parity_mode = if_.config_i.parity_mode;
                      if_.config_en_o = 1'b0;
                      if_.error_o.configuration = 1'b1;
                    end
                  end

          STD_CONFIG: begin 
                        if_.config_en_o = 1'b1;
                        state[NXT] = MAIN;

                        // Standard configuration
                        if_.config_o.data_width = STD_DATA_WIDTH;
                        if_.config_o.stop_bits = STD_STOP_BITS;
                        if_.config_o.parity_mode = STD_PARITY_MODE;
                      end

          MAIN: begin 
                  // Disable receiving and transmitting if configuring uart from the system
                  if (if_.config_en_i) begin 
                    if_.rx_fifo_write_o = 1'b0;
                    if_.rx_fifo_read_o = 1'b0;
                    if_.tx_fifo_read_o = 1'b0;
                    if_.tx_fifo_write_o = 1'b0;
                  end
                end

        endcase
      end : next_state_logic

//-----------------------//
// ERROR DETECTION LOGIC //
//-----------------------//

  // If the receiver's buffer is full and the UART is receiving data
  assign if_.error_o.overrun = (if_.is_receiving_i & if_.rx_fifo_full_i);

  logic parity;

      always_comb begin : parity_detection_logic

        // There are two types of parity checking: EVEN and ODD. Both are 
        // computed by XORing every bit of the data, the difference 
        // resides in the last bit XORed: 
        // EVEN: parity ^ 0
        // ODD:  parity ^ 1
          
        case (if_.config_i.data_width)

          DW_5BIT:  parity = ^if_.data_rx_i[4:0];

          DW_6BIT:  parity = ^if_.data_rx_i[5:0];

          DW_7BIT:  parity = ^if_.data_rx_i[6:0];

          DW_8BIT:  parity = ^if_.data_rx_i;

        endcase

        // Select ODD or EVEN parity
        case (if_.config_i.parity_mode)

          EVEN:    if_.error_o.parity = if_.parity_i != (parity ^ 1'b0);

          ODD:     if_.error_o.parity = if_.parity_i != (parity ^ 1'b1);

          default: if_.error_o.parity = 1'b0;
            
        endcase
      end : parity_detection_logic

  assign if_.error_o.frame = if_.frame_error_i;

endmodule