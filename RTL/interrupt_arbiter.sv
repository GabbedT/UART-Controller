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
// FILE NAME : interrupt_arbiter.sv
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// ------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : Arbiter for interrupt, it defines which interrupt has to be handled 
//               first, the interrupt cause signal must be high for only 1 clock cycle. 
//               After receiving the interrupt cause, the arbiter needs 2 clock cycles 
//               to signal it trough the IRQ pin. When the interrupt get cleared, 
//               the arbiter needs to wait another 2 clock cycles before signaling 
//               another possible interrupt.  
// ------------------------------------------------------------------------------------
// KEYWORDS : ENABLE INTERRUPT, PRIORITY 1 FIFO, PRIORITY 2 FIFO, PRIORITY 3 FIFO,
//            PRIORITY SELECTOR, INTERRUPT REQUEST, FSM LOGIC
// ------------------------------------------------------------------------------------

`ifndef INTERRUPT_ARBITER_INCLUDE
    `define INTERRUPT_ARBITER_INCLUDE

`include "Packages/uart_pkg.sv"
`include "sync_FIFO_buffer.sv"

module interrupt_arbiter (
    input  logic       clk_i,
    input  logic       rst_n_i,
    input  logic       rx_dsm_i,

    /* Interrupt cause */
    input  logic       rx_rdy_i,
    input  logic       tx_done_i,
    input  logic       config_error_i,
    input  logic       parity_error_i,
    input  logic       frame_error_i,
    input  logic       overrun_error_i,
    input  logic       rx_fifo_full_i,
    input  logic       config_req_slv_i,

    /* Enable interrupt */
    input  logic       overrun_error_en_i,
    input  logic       frame_error_en_i,
    input  logic       parity_error_en_i,
    input  logic       rx_rdy_en_i,

    /* Interrupt clear */
    input  logic       int_ackn_i,
    input  logic       config_ackn_i,  
    input  logic       read_rx_data_i, 
    input  logic       rx_fifo_empty_i,

    output logic [2:0] interrupt_vector_o,
    output logic       enable_int_vec_o,
    output logic       ireq_n_o
);

    /* Next and current state */
    localparam NXT = 1;
    localparam CRT = 0;


//--------------------//
//  ENABLE INTERRUPT  //
//--------------------//

    logic overrun_error, parity_error, frame_error, rx_rdy;

    assign overrun_error = overrun_error_i & overrun_error_en_i;
    assign parity_error = parity_error_i & parity_error_en_i;
    assign frame_error = frame_error_i & frame_error_en_i;

    /* The same transaction would generate two different interrupt with the same clear
     * operation. That would require two reads compromising data received */
    assign rx_rdy = (frame_error | parity_error | overrun_error) ? 1'b0 : (rx_rdy_i & rx_rdy_en_i);


//-------------------//
//  PRIORITY 1 FIFO  //
//-------------------//

    logic prio1_fifo_write;

    assign prio1_fifo_write = config_error_i | parity_error | frame_error | overrun_error;

    /* FIFO interface assignment */
    sync_fifo_interface #(4) fifo_prio1_if(clk_i);

    assign fifo_prio1_if.write_i = prio1_fifo_write;
    assign fifo_prio1_if.rst_n_i = rst_n_i;
    assign fifo_prio1_if.wr_data_i = {config_error_i, overrun_error, frame_error, parity_error};


    /* FIFO buffer instantiation in FWFT mode */
    sync_FIFO_buffer #(4, 1) priority1_fifo (clk_i, fifo_prio1_if);

    logic [3:0] prio1_data_read[NXT:CRT];

        always_ff @(posedge clk_i) begin 
            if (!rst_n_i) begin 
                prio1_data_read[CRT] <= 2'b0;
            end else begin 
                prio1_data_read[CRT] <= prio1_data_read[NXT];
            end
        end

    /* Vector generated by first priority interrupt */
    logic [2:0] prio1_int_vector;

        always_comb begin : prio1_vector_gen
            /* Internal priority:
             * -------------------------------------------------------
             *    - CONFIGURATION ERROR
             *    - OVERRUN ERROR
             *    - FRAME ERROR 
             *    - PARITY ERROR
             */
            casez (prio1_data_read[CRT])
                4'b1???: prio1_int_vector = INT_CONFIG_FAIL;
                4'b01??: prio1_int_vector = INT_OVERRUN;
                4'b001?: prio1_int_vector = INT_FRAME;
                4'b0001: prio1_int_vector = INT_PARITY;
                default: prio1_int_vector = 3'b000;
            endcase
        end : prio1_vector_gen


//-------------------//
//  PRIORITY 2 FIFO  //
//-------------------//

    logic rx_rdy_posedge;

    edge_detector #(1) rx_rdy_posedge_detector (
        .clk_i        ( clk_i          ),
        .signal_i     ( rx_rdy_i       ),
        .edge_pulse_o ( rx_rdy_posedge )
    );

    logic rx_full_posedge;

    edge_detector #(1) rx_full_posedge_detector (
        .clk_i        ( clk_i           ),
        .signal_i     ( rx_fifo_full_i  ),
        .edge_pulse_o ( rx_full_posedge )
    );

    logic prio2_fifo_write;

    assign prio2_fifo_write = rx_full_posedge | rx_rdy_posedge;

    /* FIFO interface assignment */
    sync_fifo_interface #(2) fifo_prio2_if(clk_i);

    assign fifo_prio2_if.write_i = prio2_fifo_write;
    assign fifo_prio2_if.rst_n_i = rst_n_i;
    assign fifo_prio2_if.wr_data_i = {rx_fifo_full_i, rx_rdy};

    /* FIFO buffer instantiation in FWFT mode */
    sync_FIFO_buffer #(4, 1) priority2_fifo (clk_i, fifo_prio2_if);

    logic [1:0] prio2_data_read[NXT:CRT];

        always_ff @(posedge clk_i) begin 
            if (!rst_n_i) begin 
                prio2_data_read[CRT] <= 2'b0;
            end else begin 
                prio2_data_read[CRT] <= prio2_data_read[NXT];
            end
        end

    /* Vector generated by second priority interrupt */
    logic [2:0] prio2_int_vector;

        always_comb begin : prio2_vector_gen
            /* Internal priority:
             * -------------------------------------------------------
             *    - RECEIVER FIFO FULL
             *    - REQUESTED CONFIGURATION
             */
            casez (prio2_data_read[CRT])
                2'b1?:   prio2_int_vector = INT_RX_FULL;
                2'b01:   prio2_int_vector = INT_RXD_RDY;
                default: prio2_int_vector = 3'b000;
            endcase
        end : prio2_vector_gen


//-------------------//
//  PRIORITY 3 FIFO  //
//-------------------//

    logic config_req_slv_posedge;

    edge_detector #(1) config_req_slv_posedge_detector (
        .clk_i        ( clk_i                  ),
        .signal_i     ( config_req_slv_i       ),
        .edge_pulse_o ( config_req_slv_posedge )
    );

    logic prio3_fifo_write;

    assign prio3_fifo_write = tx_done_i | config_req_slv_posedge;

    sync_fifo_interface #(2) fifo_prio3_if(clk_i);

    assign fifo_prio3_if.write_i = prio3_fifo_write;   
    assign fifo_prio3_if.rst_n_i = rst_n_i;         
    assign fifo_prio3_if.wr_data_i = {config_req_slv_i, tx_done_i};

    /* FIFO buffer instantiation in FWFT mode */
    sync_FIFO_buffer #(4, 1) priority3_fifo (clk_i, fifo_prio3_if);

    logic [1:0] prio3_data_read[NXT:CRT];

        always_ff @(posedge clk_i) begin 
            if (!rst_n_i) begin 
                prio3_data_read[CRT] <= 2'b0;
            end else begin 
                prio3_data_read[CRT] <= prio3_data_read[NXT];
            end
        end

    /* Vector generated by third priority interrupt */
    logic [2:0] prio3_int_vector;

        always_comb begin : prio3_vector_gen
            /* Internal priority:
             * -------------------------------------------------------
             *    - DATA RECEIVED READY
             *    - TRANSMISSION DONE
             */        
            casez (prio3_data_read[CRT])
                2'b1?:   prio3_int_vector = INT_CONFIG_REQ;
                2'b01:   prio3_int_vector = INT_TX_DONE;
                default: prio3_int_vector = 3'b000;
            endcase
        end : prio3_vector_gen


//---------------------//
//  PRIORITY SELECTOR  // 
//---------------------//

    localparam PRIORITY_1 = 3'b??1;
    localparam PRIORITY_2 = 3'b?10;
    localparam PRIORITY_3 = 3'b100;

    /* One hot selector */
    logic [2:0] priority_select;

    assign priority_select[0] = !fifo_prio1_if.empty_o;
    assign priority_select[1] = !fifo_prio2_if.empty_o;
    assign priority_select[2] = !fifo_prio3_if.empty_o;


//---------------------//
//  INTERRUPT REQUEST  //
//---------------------//

    logic irq_n[NXT:CRT];

        always_ff @(posedge clk_i) begin 
            if (!rst_n_i) begin 
                irq_n[CRT] <= 1'b1;
            end else begin 
                irq_n[CRT] <= irq_n[NXT];
            end
        end

    assign ireq_n_o = irq_n[CRT];


//-------------//
//  FSM LOGIC  //
//-------------//

    typedef enum logic [2:0] {
        IDLE,
        /* Wait interrupt to be cleared */
        PRIO1_WAIT_ACKN,
        PRIO2_WAIT_ACKN,
        PRIO3_WAIT_ACKN,
        /* IRQ should stay low for at least 1 clock cycle */
        PRIO1_CLEAR,
        PRIO2_CLEAR,
        PRIO3_CLEAR
    } arbiter_fsm_e;

    arbiter_fsm_e state[NXT:CRT];
  
        always_ff @(posedge clk_i) begin : fsm_state_register
            if (!rst_n_i) begin 
                state[CRT] <= IDLE;
            end else begin 
                state[CRT] <= state[NXT];
            end
        end : fsm_state_register


    logic [2:0] interrupt_vector;

    /* Enable writing vector into ISR register */
    logic enable_int_vec[NXT:CRT];

        always_ff @(posedge clk_i) begin 
            if (!rst_n_i) begin 
                enable_int_vec[CRT] <= 1'b0;
            end else begin 
                enable_int_vec[CRT] <= enable_int_vec[NXT];
            end
        end

    assign enable_int_vec_o = enable_int_vec[CRT];


        always_comb begin : fsm_next_state_logic
            irq_n[NXT] = irq_n[CRT];
            state[NXT] = state[CRT];
            prio1_data_read[NXT] = fifo_prio1_if.rd_data_o;
            prio2_data_read[NXT] = fifo_prio2_if.rd_data_o;
            prio3_data_read[NXT] = fifo_prio3_if.rd_data_o;
            fifo_prio1_if.read_i = 1'b0;
            fifo_prio2_if.read_i = 1'b0;
            fifo_prio3_if.read_i = 1'b0;
            interrupt_vector = 3'b0;
            enable_int_vec[NXT] = 1'b0;

            case (state[CRT])

                /* 
                 *  Arbiter doesn't signal any interrupt until a fifo
                 *  is not empty anymore.
                 */
                IDLE: begin 
                    irq_n[NXT] = 1'b1;

                    if (priority_select != 0) begin 
                        irq_n[NXT] = 1'b0;
                        enable_int_vec[NXT] = 1'b1;

                        /* Select the highest priority */
                        casez (priority_select)
                            PRIORITY_1: begin 
                                fifo_prio1_if.read_i = 1'b1;
                                state[NXT] = PRIO1_WAIT_ACKN;
                            end

                            PRIORITY_2: begin 
                                fifo_prio2_if.read_i = 1'b1;
                                state[NXT] = PRIO2_WAIT_ACKN;
                            end

                            PRIORITY_3: begin 
                                fifo_prio3_if.read_i = 1'b1;
                                state[NXT] = PRIO3_WAIT_ACKN;
                            end
                        endcase
                    end
                end


                /*
                 *  Wait for the acknowledge of the first priority interrupt.
                 */
                PRIO1_WAIT_ACKN: begin 
                    interrupt_vector = prio1_int_vector;

                    case (interrupt_vector)
                        INT_CONFIG_FAIL: begin 
                            if (int_ackn_i) begin 
                                prio1_data_read[NXT] = {1'b0, prio1_data_read[CRT][2:0]};
                                state[NXT] = PRIO1_CLEAR;
                                irq_n[NXT] = 1'b1;
                            end              
                        end

                        /* Those 3 interrupt require a data read, that will clear 
                        * the other ones too if there are multiple interrupt in
                        * a transaction. */
                        INT_OVERRUN, INT_FRAME, INT_PARITY: begin 
                            if (read_rx_data_i) begin 
                                state[NXT] = PRIO1_CLEAR;
                                irq_n[NXT] = 1'b1;
                            end 
                        end              
                    endcase
                end


                /*
                 *  Wait for the acknowledge of the second priority interrupt.
                 */
                PRIO2_WAIT_ACKN: begin 
                    interrupt_vector = prio2_int_vector;

                    case (interrupt_vector)
                        INT_RX_FULL: begin 
                            if ((rx_dsm_i & rx_fifo_empty_i) | (!rx_dsm_i & read_rx_data_i)) begin 
                                prio2_data_read[NXT] = {1'b0, prio2_data_read[CRT][0]};
                                state[NXT] = PRIO2_CLEAR;
                                irq_n[NXT] = 1'b1;
                            end               
                        end

                        INT_RXD_RDY: begin 
                            if ((rx_dsm_i & rx_fifo_empty_i) | (!rx_dsm_i & read_rx_data_i)) begin 
                                prio2_data_read[NXT] = {prio3_data_read[CRT][1], 1'b0};
                                state[NXT] = PRIO2_CLEAR;
                                irq_n[NXT] = 1'b1;
                            end              
                        end
                    endcase
                end


                /*
                 *  Wait for the acknowledge of the third priority interrupt.
                 */
                PRIO3_WAIT_ACKN: begin 
                    interrupt_vector = prio3_int_vector;

                    case (interrupt_vector)
                        INT_CONFIG_REQ: begin 
                            if (config_ackn_i) begin
                                prio3_data_read[NXT] = {1'b0, prio3_data_read[CRT][0]};
                                state[NXT] = PRIO3_CLEAR;
                                irq_n[NXT] = 1'b1;
                            end 
                        end

                        INT_TX_DONE: begin
                            if (int_ackn_i) begin 
                                prio3_data_read[NXT] = {prio3_data_read[CRT][1], 1'b0};
                                state[NXT] = PRIO3_CLEAR;
                                irq_n[NXT] = 1'b1;
                            end
                        end              
                    endcase
                end


                /*
                 *  Clear first priority interrupt (IRQ stay high for at least one clock cycle).
                 *  Wait again if there's another interrupt of the same priority 
                 */
                PRIO1_CLEAR: begin 
                    if (interrupt_vector[CRT] != 0) begin 
                        state[NXT] = PRIO1_WAIT_ACKN;
                        irq_n[NXT] = 1'b0;
                    end else begin 
                        state[NXT] = IDLE;
                    end
                end


                /*
                 *  Clear second priority interrupt (IRQ stay high for at least one clock cycle).
                 *  Wait again if there's another interrupt of the same priority 
                 */
                PRIO2_CLEAR: begin 
                    if (interrupt_vector[CRT] != 0) begin 
                        state[NXT] = PRIO2_WAIT_ACKN;
                        irq_n[NXT] = 1'b0;
                    end else begin 
                        state[NXT] = IDLE;
                    end
                end


                /*
                 *  Clear third priority interrupt (IRQ stay high for at least one clock cycle).
                 *  Wait again if there's another interrupt of the same priority 
                 */
                PRIO3_CLEAR: begin 
                    if (interrupt_vector[CRT] != 0) begin 
                        state[NXT] = PRIO3_WAIT_ACKN;
                        irq_n[NXT] = 1'b0;
                    end else begin 
                        state[NXT] = IDLE;
                    end
                end

            endcase
        end : fsm_next_state_logic

    assign interrupt_vector_o = interrupt_vector;

endmodule : interrupt_arbiter 

`endif