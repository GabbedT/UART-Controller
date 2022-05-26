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
// FILE NAME : UART_pkg.sv
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// ------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : This package contains UART parameters. 
// ------------------------------------------------------------------------------------
// KEYWORDS : GENERAL PARAMETERS
// ------------------------------------------------------------------------------------

`ifndef UART_PACKAGE
  `define UART_PACKAGE

package UART_pkg;

//------------------------------//
//  PACKET WIDTH CONFIGURATION  //
//------------------------------//

  /* Command ID */
  localparam logic [1:0] DATA_WIDTH_ID = 2'b01;

  /* Configuration code */
  localparam logic [1:0] DW_5BIT = 2'b00;
  localparam logic [1:0] DW_6BIT = 2'b01;
  localparam logic [1:0] DW_7BIT = 2'b10;
  localparam logic [1:0] DW_8BIT = 2'b11;


//-----------------------------//
//  PARITY MODE CONFIGURATION  //
//-----------------------------//

  /* Command ID */
  localparam logic [1:0] PARITY_MODE_ID = 2'b10;

  /* Configuration code */
  localparam logic [1:0] EVEN       = 2'b00;
  localparam logic [1:0] ODD        = 2'b01;
  localparam logic [1:0] DISABLED1  = 2'b10;
  localparam logic [1:0] DISABLED2  = 2'b11;


//---------------------------//
//  STOP BITS CONFIGURATION  //
//---------------------------// 

  /* Command ID */
  localparam logic [1:0] STOP_BITS_ID = 2'b11;
  
  /* Configuration code */
  localparam logic [1:0] SB_1BIT   = 2'b00;
  localparam logic [1:0] SB_2BIT   = 2'b01;
  localparam logic [1:0] RESERVED1 = 2'b10;
  localparam logic [1:0] RESERVED2 = 2'b11;


//-----------------------------//
//  END CONFIGURATION PROCESS  //
//-----------------------------//

  localparam logic [1:0] END_CONFIGURATION_ID = 2'b00;


//-----------------//
//  INTERRUPT IDS  //
//-----------------//

  /* Interrupt id */
  localparam INT_CONFIG_FAIL = 3'b000;
  localparam INT_OVERRUN     = 3'b001;
  localparam INT_FRAME       = 3'b010;
  localparam INT_PARITY      = 3'b011;
  localparam INT_RXD_RDY     = 3'b100;
  localparam INT_RX_FULL     = 3'b101;
  localparam INT_CONFIG_REQ  = 3'b110;
  localparam INT_TX_DONE     = 3'b111;


//----------------------//
//  COMMUNICATION MODE  //
//----------------------//

  /* Communication mode */
  localparam DISABLED    = 2'b00;
  localparam SIMPLEX_TX  = 2'b01;
  localparam SIMPLEX_RX  = 2'b10;
  localparam FULL_DUPLEX = 2'b11;

  localparam STD_COMM_MODE = FULL_DUPLEX;


//----------------------//
//  GENERAL PARAMETERS  //
//----------------------//

  /* System clock frequency in Hz */
  localparam SYSTEM_CLOCK_FREQ = 100_000_000;

  /* Number of words stored in the buffers */
  localparam TX_FIFO_DEPTH = 64;
  localparam RX_FIFO_DEPTH = 64;

  /* Number of SYN character received to detect the 
   * start of the configuration request */
  localparam SYN_NUMBER = 3;

  /* Standard configuration */
  localparam STD_DATA_WIDTH  = DW_8BIT;
  localparam STD_STOP_BITS   = SB_1BIT;
  localparam STD_PARITY_MODE = EVEN;

  localparam STD_CONFIGURATION = {STD_STOP_BITS, STD_PARITY_MODE, STD_DATA_WIDTH};

  /* Standard baud rate */
  localparam STD_BAUD_RATE = 9600;

  localparam STD_DIVISOR = int'((SYSTEM_CLOCK_FREQ / (16 * STD_BAUD_RATE)) - 1);


//----------------------//
//  MODULES PARAMETERS  //
//----------------------//

  /* How many clock cycles does it need to reach 1 ms */ 
  /* based on a specific system clock */
  localparam COUNT_1MS = SYSTEM_CLOCK_FREQ / 1000;

  localparam READ = 1;
  localparam WRITE = 0;

endpackage : UART_pkg

`endif 