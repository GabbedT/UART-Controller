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
// FILE NAME : main_controller_pkg.sv
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// ------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : This package contains main controller parameters and typedefs. 
// ------------------------------------------------------------------------------------
// KEYWORDS : DATA PACKET, PACKET WIDTH CONFIGURATION, PARITY MODE CONFIGURATION,
//            STOP BITS CONFIGURATION, END CONFIGURATION PROCESS
// ------------------------------------------------------------------------------------

`ifndef MAIN_CONTROLLER_PKG
  `define MAIN_CONTROLLER_PKG

package main_controller_pkg;

  localparam ACKN_PKT = 8'hFF; 

//---------------//
//  DATA PACKET  //
//---------------//

  /*
   * Normally the data packet is just composed by 8 bit of data.
   * Data packet received from UART Host to CONFIGURE the device. 
   * is composed by 3 parts:
   *
   * COMMAND ID: bits [1:0] specifies the setting to configure
   * OPTION:     bits [3:2] select an option
   * DON'T CARE: bits [7:4] those bits are simply ignored
   */
  typedef struct packed {
    logic [3:0] dont_care;
    logic [1:0] option;
    logic [1:0] id;
  } configuration_packet_s;


  /* The packet can have 2 different rapresentation thus it's expressed as union */
  typedef union packed {
    /* Main state */
    logic [7:0] packet;
    /* Configuration state */
    configuration_packet_s cfg_packet;
  } data_packet_u;


  typedef struct packed {
    logic [1:0] data_width;
    logic [1:0] parity_mode;
    logic [1:0] stop_bits;
  } uart_config_s;


  function logic [7:0] assemble_packet(input logic [1:0] id, input logic [1:0] option);
    return {4'b0, option, id};
  endfunction : assemble_packet

  /* ASCII synchronous idle character */
  localparam SYN = 8'h16;

endpackage : main_controller_pkg

`endif 