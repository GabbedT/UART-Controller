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

module interrupt_arbiter (
    input  logic       clk_i,
    input  logic       rst_n_i,
    input  logic       rx_dsm_i,            // From REGISTERS
    input  logic       disable_interrupts_i, // From CONTROL UNIT

    /* Interrupt cause */
    input  logic       rx_rdy_i,        // From RECEIVER
    input  logic       tx_done_i,       // From TRANSMITTER
    input  logic       config_error_i,  // From CONTROL UNIT
    input  logic       parity_error_i,  // From RECEIVER
    input  logic       frame_error_i,   // From RECEIVER
    input  logic       overrun_error_i, // From RECEIVER
    input  logic       rx_fifo_full_i,  // From RECEIVER
    input  logic       config_req_slv_i,// From RECEIVER

    /* Enable interrupt */
    input  logic       overrun_error_en_i,  // From REGISTERS
    input  logic       frame_error_en_i,    // From REGISTERS
    input  logic       parity_error_en_i,   // From REGISTERS
    input  logic       rx_rdy_en_i,         // From REGISTERS
    input  logic       tx_done_en_i,        // From REGISTERS

    /* Interrupt clear */
    input  logic       int_ackn_i,      // From TOP
    input  logic       read_rx_data_i,  // From REGISTERS
    input  logic       rx_fifo_empty_i, // From RECEIVER

    output logic [2:0] interrupt_vector_o,      // To REGISTERS
    output logic       store_int_vect_o,   // To REGISTERS
    output logic       ireq_n_o                 // To TOP
);

    /* Next and current state */
    localparam NXT = 1;
    localparam CRT = 0;


//--------------------//
//  ENABLE INTERRUPT  //
//--------------------//

    logic overrun_error, parity_error, frame_error, rx_rdy, tx_done;

    assign tx_done = tx_done_i & tx_done_en_i;
    assign overrun_error = overrun_error_i & overrun_error_en_i;
    assign parity_error = parity_error_i & parity_error_en_i;
    assign frame_error = frame_error_i & frame_error_en_i;

    /* The same transaction would generate two different interrupt with the same clear
     * operation. That would require two reads compromising data received */
    assign rx_rdy = (frame_error | parity_error | overrun_error) ? 1'b0 : (rx_rdy_i & rx_rdy_en_i);


//--------------------//
//  PRIORITY 1 LOGIC  //
//--------------------//

    /* Interrupt location in the bundle */
    localparam CFG_ERROR = 3;
    localparam OVR_ERROR = 2;
    localparam FRM_ERROR = 1;
    localparam PAR_ERROR = 0;

    /* Register control nets */
    logic       p1_enable_load;
    logic [3:0] p1_reset;

    /* Store interrupt bundle */
    logic [3:0] p1_int_bundle_CRT, p1_int_bundle_NXT;

    genvar i;
    generate 
        
        for (i = 0; i < 4; ++i) begin 
            always_ff @(posedge clk_i or negedge rst_n_i) begin  
                if (!rst_n_i) begin 
                    p1_int_bundle_CRT[i] <= 1'b0;
                end else if (p1_reset[i] | disable_interrupts_i) begin 
                    p1_int_bundle_CRT[i] <= 1'b0;
                end else if (p1_enable_load) begin 
                    p1_int_bundle_CRT[i] <= p1_int_bundle_NXT[i];
                end
            end 
        end

    endgenerate

    assign p1_int_bundle_NXT = {config_error_i, overrun_error, frame_error, parity_error};
    assign p1_enable_load = |p1_int_bundle_NXT;


    /* Vector generated by first priority interrupt */
    logic [2:0] p1_int_vector;

        always_comb begin : prio1_vector_gen
            /* Internal priority:
             * -------------------------------------------------------
             *    - CONFIGURATION ERROR
             *    - OVERRUN ERROR
             *    - FRAME ERROR 
             *    - PARITY ERROR
             */
            casez (p1_int_bundle_CRT)
                4'b1???: p1_int_vector = INT_CONFIG_FAIL;
                4'b01??: p1_int_vector = INT_OVERRUN;
                4'b001?: p1_int_vector = INT_FRAME;
                4'b0001: p1_int_vector = INT_PARITY;
                default: p1_int_vector = 3'b000;
            endcase
        end : prio1_vector_gen


//-------------------//
//  PRIORITY 2 FIFO  //
//-------------------//

    localparam RX_FULL = 1;
    localparam RX_RDY = 0;

    logic       p2_enable_load;
    logic [1:0] p2_reset;

    /* Store interrupt bundle */
    logic [1:0] p2_int_bundle_CRT, p2_int_bundle_NXT;

    genvar j;
    generate 
        
        for (j = 0; j < 2; ++j) begin 
            always_ff @(posedge clk_i or negedge rst_n_i) begin  
                if (!rst_n_i) begin 
                    p2_int_bundle_CRT[j] <= 1'b0;
                end else if (p2_reset[j] | disable_interrupts_i) begin
                    p2_int_bundle_CRT[j] <= 1'b0;
                end else if (p2_enable_load) begin 
                    p2_int_bundle_CRT[j] <= p2_int_bundle_NXT[j];
                end
            end 
        end

    endgenerate

    assign p2_int_bundle_NXT = {rx_fifo_full_i, rx_rdy};
    assign p2_enable_load = |p2_int_bundle_NXT;


    /* Vector generated by second priority interrupt */
    logic [2:0] p2_int_vector;

        always_comb begin : prio2_vector_gen
            /* Internal priority:
             * -------------------------------------------------------
             *    - RECEIVER FIFO FULL
             *    - REQUESTED CONFIGURATION
             */
            casez (p2_int_bundle_CRT)
                2'b1?:   p2_int_vector = INT_RX_FULL;
                2'b01:   p2_int_vector = INT_RXD_RDY;
                default: p2_int_vector = 3'b000;
            endcase
        end : prio2_vector_gen


//-------------------//
//  PRIORITY 3 FIFO  //
//-------------------//

    localparam CFG_REQ = 1;
    localparam TX_DONE = 0;

    logic       p3_enable_load;
    logic [1:0] p3_reset;

    /* Store interrupt bundle */
    logic [1:0] p3_int_bundle_CRT, p3_int_bundle_NXT;

    genvar k;
    generate 
        
        for (k = 0; k < 2; ++k) begin 
            always_ff @(posedge clk_i or negedge rst_n_i) begin  
                if (!rst_n_i) begin 
                    p3_int_bundle_CRT[k] <= 1'b0;
                end else if (p3_reset[k] | disable_interrupts_i) begin 
                    p3_int_bundle_CRT[k] <= 1'b0;
                end else if (p3_enable_load) begin 
                    p3_int_bundle_CRT[k] <= p3_int_bundle_NXT[k];
                end
            end 
        end

    endgenerate

    assign p3_int_bundle_NXT = {config_req_slv_i, tx_done};
    assign p3_enable_load = |p3_int_bundle_NXT;


    /* Vector generated by third priority interrupt */
    logic [2:0] p3_int_vector;

        always_comb begin : prio3_vector_gen
            /* Internal priority:
             * -------------------------------------------------------
             *    - DATA RECEIVED READY
             *    - TRANSMISSION DONE
             */        
            casez (p3_int_bundle_CRT)
                2'b1?:   p3_int_vector = INT_CONFIG_REQ;
                2'b01:   p3_int_vector = INT_TX_DONE;
                default: p3_int_vector = 3'b000;
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

    assign priority_select[0] = |p1_int_bundle_NXT;
    assign priority_select[1] = |p2_int_bundle_NXT;
    assign priority_select[2] = |p3_int_bundle_NXT;


//-------------//
//  FSM LOGIC  //
//-------------//

    normal_interrupt_response_fsm_e state_CRT, state_NXT;
  
        always_ff @(posedge clk_i or negedge rst_n_i) begin : fsm_state_register
            if (!rst_n_i) begin 
                state_CRT <= IDLE;
            end else if (disable_interrupts_i) begin 
                state_CRT <= IDLE;
            end else begin 
                state_CRT <= state_NXT;
            end
        end : fsm_state_register


    logic interrupt_clear, interrupt_set;

        always_ff @(posedge clk_i or negedge rst_n_i) begin 
            if (!rst_n_i) begin
                ireq_n_o <= 1'b1;
            end else if (interrupt_set) begin
                ireq_n_o <= 1'b0;
            end else if (interrupt_clear) begin
                ireq_n_o <= 1'b1;
            end
        end


    logic [2:0] interrupt_vector;

        always_comb begin : fsm_next_state_logic
            state_NXT = state_CRT;

            p1_reset = 4'b0;
            p2_reset = 2'b0;
            p3_reset = 2'b0;

            // p1_enable_load = 1'b0;
            // p2_enable_load = 1'b0;
            // p3_enable_load = 1'b0;

            interrupt_vector = 3'b0;
            store_int_vect_o = 1'b0;
            
            interrupt_set = 1'b0;
            interrupt_clear = 1'b0;
            
            casez (priority_select)
                PRIORITY_1: interrupt_vector = p1_int_vector;
                PRIORITY_2: interrupt_vector = p2_int_vector;
                PRIORITY_3: interrupt_vector = p3_int_vector;
                default:    interrupt_vector = 3'b0;
            endcase

            case (state_CRT)

                /* 
                 *  Arbiter doesn't signal any interrupt until a fifo
                 *  is not empty anymore.
                 */
                IDLE: begin 
                    if (priority_select != 0) begin 
                        interrupt_set = 1'b1;
                        store_int_vect_o = 1'b1;

                        /* Select the highest priority */
                        casez (priority_select)
                            PRIORITY_1: begin 
                                state_NXT = PRIO1_WAIT_ACKN;
                            end

                            PRIORITY_2: begin 
                                state_NXT = PRIO2_WAIT_ACKN;
                            end

                            PRIORITY_3: begin 
                                state_NXT = PRIO3_WAIT_ACKN;
                            end
                        endcase
                    end
                end


                /*
                 *  Wait for the acknowledge of the first priority interrupt.
                 */
                PRIO1_WAIT_ACKN: begin 
                    /* Clear interrupt */
                    if (int_ackn_i) begin
                        interrupt_clear = 1'b1;
                    end


                    case (interrupt_vector)
                        INT_CONFIG_FAIL: begin 
                            if (int_ackn_i) begin 
                                p1_reset[CFG_ERROR] = 1'b1;
                                state_NXT = PRIO1_CLEAR;
                            end              
                        end

                        /* Those 3 interrupt require a data read, that will clear 
                         * the other ones too if there are multiple interrupt in
                         * a transaction. */
                        INT_OVERRUN, INT_FRAME, INT_PARITY: begin 
                            if (read_rx_data_i) begin 
                                p1_reset[OVR_ERROR] = 1'b1;
                                p1_reset[FRM_ERROR] = 1'b1;
                                p1_reset[PAR_ERROR] = 1'b1;
                                p2_reset[RX_RDY] = 1'b1;
                                state_NXT = PRIO1_CLEAR;
                            end 
                        end              
                    endcase
                end


                /*
                 *  Wait for the acknowledge of the second priority interrupt.
                 */
                PRIO2_WAIT_ACKN: begin 
                    /* Clear interrupt */
                    if (int_ackn_i) begin
                        interrupt_clear = 1'b1;
                    end


                    case (interrupt_vector)
                        INT_RX_FULL: begin 
                            if ((rx_dsm_i & rx_fifo_empty_i) | (!rx_dsm_i & read_rx_data_i)) begin 
                                p2_reset[RX_FULL] = 1'b1;
                                state_NXT = PRIO2_CLEAR;
                            end               
                        end

                        INT_RXD_RDY: begin 
                            if ((rx_dsm_i & rx_fifo_empty_i) | (!rx_dsm_i & read_rx_data_i)) begin 
                                p2_reset[RX_RDY] = 1'b1;
                                state_NXT = PRIO2_CLEAR;
                            end              
                        end
                    endcase
                end


                /*
                 *  Wait for the acknowledge of the third priority interrupt.
                 */
                PRIO3_WAIT_ACKN: begin 
                    /* Clear interrupt */
                    if (int_ackn_i) begin
                        interrupt_clear = 1'b1;
                    end


                    case (interrupt_vector)
                        INT_CONFIG_REQ: begin 
                            if (int_ackn_i) begin
                                p3_reset[CFG_REQ] = 1'b1;
                                state_NXT = PRIO3_CLEAR;
                            end 
                        end

                        INT_TX_DONE: begin
                            if (int_ackn_i) begin 
                                p3_reset[TX_DONE] = 1'b1;
                                state_NXT = PRIO3_CLEAR;
                            end
                        end              
                    endcase
                end


                /*
                 *  Transition state between an interrupt and another of the same bundle
                 */
                PRIO1_CLEAR: begin 
                    if (p1_int_bundle_CRT != 0) begin 
                        state_NXT = PRIO1_WAIT_ACKN;
                        interrupt_set = 1'b1;
                    end else begin 
                        state_NXT = IDLE;
                    end
                end


                /*
                 *  Transition state between an interrupt and another of the same bundle
                 */
                PRIO2_CLEAR: begin 
                    if (p2_int_bundle_CRT != 0) begin 
                        state_NXT = PRIO2_WAIT_ACKN;
                        interrupt_set = 1'b1;
                    end else begin 
                        state_NXT = IDLE;
                    end
                end


                /*
                 *  Transition state between an interrupt and another of the same bundle
                 */
                PRIO3_CLEAR: begin 
                    if (p3_int_bundle_CRT != 0) begin 
                        state_NXT = PRIO3_WAIT_ACKN;
                        interrupt_set = 1'b1;
                    end else begin 
                        state_NXT = IDLE;
                    end
                end

            endcase
        end : fsm_next_state_logic

    assign interrupt_vector_o = interrupt_vector;

endmodule : interrupt_arbiter 

`endif