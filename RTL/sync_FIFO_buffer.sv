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
// FILE NAME : FIFO_buffer_sync.sv
// DEPARTMENT : 
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// ------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : This is a parametrizable syncronous FIFO buffer, it is implemented as 
//               a circular queue using two pointers for read and write operation. 
//               It is composed by two parts: the controller and the memory.
//               The operation are: READ and WRITE, it's possible to simultaneusly
//               read and write. The "read_i" signal mustn't be asserted when the signal
//               "empty_o" is true and the "write_i" signal mustn't be asserted when the
//               signal "full_o" is true. Note that empty/full signal are asserted 
//               immediatly as the control signal arrives, not in the next clock cycle!
// ------------------------------------------------------------------------------------
// KEYWORDS : FWFT_configuration, standard_configuration, status_register, 
//            next_state_logic
// ------------------------------------------------------------------------------------
// DEPENDENCIES: sync_fifo_interface.sv 
// ------------------------------------------------------------------------------------
// PARAMETERS
//
// PARAM NAME : RANGE : DESCRIPTION                 : DEFAULT VALUE
// ------------------------------------------------------------------------------------
// FIFO_DEPTH :   /   : Total word stored           : 32
// FWFT       : [1:0] : Use FWFT config or standard : 1
// ------------------------------------------------------------------------------------

`include "sync_FIFO_interface.sv"

module sync_FIFO_buffer #(
    /* Total word stored in memory */
    parameter int FIFO_DEPTH = 32,

    /* 
     * Use FWFT configuration or standard.
     * In FWFT (First Word Fall Through) the head of
     * the FIFO is available in the read port as soon
     * as the "read_i" signal is asserted 
     */
    parameter int FWFT = 1
) 
( input logic clk_i, sync_fifo_interface.pinout intf ); 
  
//------------//
// PARAMETERS //
//------------//

    /* Current and next */
    localparam CRT = 0;
    localparam NXT = 1;

    /* Address bits for fifo memory */
    localparam ADDR_BITS = $clog2(FIFO_DEPTH);

    /* FIFO access mode */
    localparam logic [1:0] READ  = 2'b01;
    localparam logic [1:0] WRITE = 2'b10;
    localparam logic [1:0] BOTH  = 2'b11;

//--------------//
// MEMORY LOGIC //
//--------------//

    /* Write and read address, they are driven by the controller pointers */
    logic [ADDR_BITS - 1:0] wr_addr, rd_addr;

    /* Fifo status */
    logic full, empty;

    /* Enable signal for read and write operations */
    logic write_en, read_en;

    /* Memory block */
    logic [intf.DATA_WIDTH - 1:0] FIFO_memory [FIFO_DEPTH - 1:0];

    /* The syncronous fifo writes a word on positive edge of the clock,  
     * read depends on the FWFT parameters */
    generate
    
        /* Memory instantiation */
        if (FWFT == 1) begin : FWFT_configuration
            always_ff @(posedge clk_i or negedge rst_n_i) begin 
                if (write_en) begin 
                    FIFO_memory[wr_addr] <= intf.wr_data_i; 
                end
            end

            /* The read is asyncronous */
            assign intf.rd_data_o = FIFO_memory[rd_addr];
        end : FWFT_configuration

    else begin : standard_configuration
        /* The read is syncronous */
        always_ff @(posedge clk_i or negedge rst_n_i) begin 
            if (write_en & read_en) begin 
                FIFO_memory[wr_addr] <= intf.wr_data_i; 
                intf.rd_data_o <= FIFO_memory[rd_addr];
            end else if (read_en) begin 
                intf.rd_data_o <= FIFO_memory[rd_addr];
            end else if (write_en) begin
                FIFO_memory[wr_addr] <= intf.wr_data_i; 
            end
        end
    end : standard_configuration

  endgenerate

//------------------//
// CONTROLLER LOGIC //
//------------------//

    /* Pointers declaration */
    logic [ADDR_BITS - 1:0] write_ptr[NXT:CRT]; 
    logic [ADDR_BITS - 1:0] read_ptr[NXT:CRT];

    /* Incremented pointer */
    logic [ADDR_BITS - 1:0] write_ptr_inc, read_ptr_inc;

    /* Enable the write only when the fifo is not full */
    assign write_en = intf.write_i & !intf.full_o;

    /* Enable the read only when the fifo is not empty */
    assign read_en = intf.read_i & !intf.empty_o;

    assign wr_addr = write_ptr[CRT];
    assign rd_addr = read_ptr[CRT];

        always_ff @(posedge clk_i or negedge rst_n_i) begin : status_register
            if (!intf.rst_n_i) begin 
                write_ptr[CRT] <= 'b0;
                read_ptr[CRT] <= 'b0;
                intf.full_o <= 1'b0;
                intf.empty_o <= 1'b1;
            end else begin 
                write_ptr[CRT] <= write_ptr[NXT];
                read_ptr[CRT] <= read_ptr[NXT];
                intf.full_o <= full;
                intf.empty_o <= empty;
            end
        end : status_register

    generate
    
        /* If FIFO DEPTH is a power of two */
        if (FIFO_DEPTH == (2**($clog2(FIFO_DEPTH)))) begin 
            assign write_ptr_inc = write_ptr[CRT] + 1;
            assign read_ptr_inc = read_ptr[CRT] + 1;
        end else begin 
            assign write_ptr_inc = (write_ptr[CRT] == (FIFO_DEPTH - 1)) ? 'b0 : write_ptr[CRT] + 1'b1;
            assign read_ptr_inc = (read_ptr[CRT] == (FIFO_DEPTH - 1)) ? 'b0 : read_ptr[CRT] + 1'b1;
        end

    endgenerate

        always_comb begin : next_state_logic
        
            //------------------//
            //  DEFAULT VALUEs  //
            //------------------//

            write_ptr[NXT] = write_ptr[CRT];
            read_ptr[NXT] = read_ptr[CRT];
            empty = intf.empty_o;
            full = intf.full_o;
          
            case ({intf.write_i, intf.read_i})
                READ: begin 
                    if (!intf.empty_o) begin 
                        /* Increment the read pointer */
                        read_ptr[NXT] = read_ptr_inc;

                        /* If there's only a read the fifo will never be full */
                        full = 1'b0;

                        /* Since this fifo is a circular queue, when we read and
                         * the two pointers are equals it means that the fifo is empty */
                        empty = (write_ptr[CRT] == read_ptr_inc);
                        write_ptr[NXT] = write_ptr[CRT];
                    end 
                end

                WRITE: begin 
                    if (!intf.full_o) begin 
                        /* Increment the write pointer */
                        write_ptr[NXT] = write_ptr_inc;
                                    
                        /* If there's only a write the fifo will never be empty */
                        empty = 1'b0;
                                
                        /* Since this fifo is a circular queue, when we write and
                         * the two pointers are equals it means that the fifo is full */
                        full = (read_ptr[CRT] == write_ptr_inc);
                        read_ptr[NXT] = read_ptr[CRT];
                    end 
                end

                BOTH: begin 
                    /* Increment the write and read pointer */
                    write_ptr[NXT] = write_ptr_inc;
                    read_ptr[NXT] = read_ptr_inc;
                end
            endcase

        end : next_state_logic

endmodule : sync_FIFO_buffer