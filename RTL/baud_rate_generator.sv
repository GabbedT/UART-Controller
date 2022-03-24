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
// FILE NAME : baud_rate_generator.sv
// DEPARTMENT : 
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// ------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : This module is effectively a simple counter. It doesn't calculate the 
//               effective baud rate frequency but a multiple of it. Precisely it 
//               generate a clock which has 16 time the baud rate frequency. For a 
//               precise baud rate exist a precise divisor value which is caluclated 
//               by: divisor = (sys_clock_freq / (16 * baud_rate)) - 1. The divisor is 
//               then used by this module to generate a clock.
//               The clock has to be 16 times the baud rate so it's possible to utilize
//               the "oversampling" strategy.
//               Additionally it contains a counter that ticks at the baud rate freq.
// ------------------------------------------------------------------------------------
// KEYWORDS : 
// ------------------------------------------------------------------------------------
// DEPENDENCIES :  
// ------------------------------------------------------------------------------------
// PARAMETERS
// PARAM NAME : RANGE : DESCRIPTION            : DEFAULT 
// DVSR_WIDTH :   /   : Divisor number of bits : 32
// ------------------------------------------------------------------------------------

module baud_rate_generator #(

  /* Divisor's number of bits used to calculate the baud rate */
  parameter DVSR_WIDTH = 16
) 
(
  input  logic                    clk_i,
  input  logic                    rst_n_i,
  input  logic [DVSR_WIDTH - 1:0] divisor_i,

  output logic                    ov_baud_rt_o 
);

//----------//
// DATAPATH //
//----------//

  /* Counter for oversampling */
  logic [DVSR_WIDTH - 1:0] counter_ov;

  /* Counter that ticks 16 times the baudrate */
  always_ff @(posedge clk_i) begin : counter_16_br
    if (!rst_n_i) begin 
      counter_ov <= 'b0; 
    end else begin  
      /* Reset if the counter reach the divisor value */
      counter_ov <= (counter_ov == divisor_i) ? 'b0 : counter_ov + 1'b1;
    end
  end : counter_16_br

  /* The counter counts from 0 to divisor value so it actually counts divisor + 1 times
   * thus the clock generated should tick only when it reach the value 1 */
  assign ov_baud_rt_o = (counter_ov == 1);
  
endmodule