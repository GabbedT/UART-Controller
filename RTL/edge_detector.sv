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
// FILE NAME : edge_detector.sv
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// ------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : Edge detector module   
// ------------------------------------------------------------------------------------

module edge_detector #(
    /* 
    * 1 = Positive Edge
    * 0 = Negative Edge 
    */
    parameter EDGE = 1
) (
    input  logic clk_i,
    input  logic signal_i,

    output logic edge_pulse_o
);

    /* Memorize the signal value of the previous clock cycle */
    logic signal_dly;

        always_ff @(posedge clk_i or negedge rst_n_i) begin : delay 
            signal_dly <= signal_i;
        end : delay
    
    if (EDGE) begin
        /* Detect positive edge */
        assign edge_pulse_o = signal_i & (!signal_dly);
    end else begin 
        /* Detect negative edge */
        assign edge_pulse_o = (!signal_i) & signal_dly;
    end

endmodule : edge_detector