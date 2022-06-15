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
// FILE NAME : control_unit.sv
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
// KEYWORDS : PARAMETERS, DATAPATH, FSM LOGIC, ERROR DETECTION LOGIC, 
//            COMMUNICATION MODE, ASSERTIONS
// ------------------------------------------------------------------------------------

`ifndef CONTROL_UNIT_INCLUDE
    `define CONTROL_UNIT_INCLUDE

`include "Packages/uart_pkg.sv"

module control_unit ( 
    input  logic         rst_n_i,
    input  logic         clk_i,         
    
    /* Data */
    input  data_packet_u data_rx_i,     
    input  logic [7:0]   data_tx_i,     
    
    /* Transmitter */
    input  logic         tx_done_i,     
    input  logic         req_done_i,       
    
    /* FIFO status */ 
    input  logic         rx_fifo_empty_i,    
    input  logic         rx_fifo_read_i,    
    input  logic         tx_fifo_full_i,
    input  logic         tx_fifo_write_i,   
    
    /* Configuration */
    input  logic         request_ack_i,
    input  logic         enable_config_receive_i,   
    input  logic         config_req_slv_i,           
    input  logic         config_req_mst_i,          
    input  uart_config_s config_i,                  
    input  uart_config_s updated_config_i,          

    output logic         STR_en_o,                  
    output uart_config_s config_o,                  
    output logic         config_req_mst_o,          
    output logic         set_std_config_o,          
    output logic         config_done_o,                 
    output logic         disable_global_int_o,               
    
    /* FIFO operations */
    output logic         rx_fifo_read_o,            
    output logic         tx_fifo_write_o,          
    
    /* Data */
    output logic [7:0]   data_tx_o,               
    
    /* Error */
    output logic         config_error_o   
);

//------------//
//  DATAPATH  //
//------------//

    /* Counter to 50ms */
    logic [$clog2(COUNT_10MS) - 1:0] counter_10ms_CRT, counter_10ms_NXT;

        always_ff @(posedge clk_i or negedge rst_n_i) begin : ms50_counter
            if (!rst_n_i) begin   
                counter_10ms_CRT <= 'b0;
            end else if (counter_10ms_CRT == COUNT_10MS) begin  
                counter_10ms_CRT <= 'b0;
            end else begin
                counter_10ms_CRT <= counter_10ms_NXT;
            end
        end : ms50_counter


    /* Number of times the configuration failed */
    logic [1:0] config_failed_CRT, config_failed_NXT;

    /* Tracks the state of the configuration */
    logic [1:0] config_packet_type_CRT, config_packet_type_NXT;

    localparam DW_TYPE = 2'b00;  /* Data width        */
    localparam PM_TYPE = 2'b01;  /* Parity mode       */
    localparam SB_TYPE = 2'b10;  /* Stop bits         */
    localparam EC_TYPE = 2'b11;  /* End configuration */

    /* Count the number of SYN character sended */
    logic [$clog2(SYN_NUMBER) - 1:0] syn_data_cnt_CRT, syn_data_cnt_NXT;  
    
        /* Count the number of times the device has tried to reques a configuration
         * and the slave device didn't respond (max 3 times) */
        always_ff @(posedge clk_i or negedge rst_n_i) begin : datapath_register
            if (!rst_n_i) begin 
                config_failed_CRT <= 'b0;
                config_packet_type_CRT <= 'b0;
                syn_data_cnt_CRT <= 2'b0;
            end else begin 
                config_failed_CRT <= config_failed_NXT;
                config_packet_type_CRT <= config_packet_type_NXT;
                syn_data_cnt_CRT <= syn_data_cnt_NXT;
            end
        end : datapath_register


    /* Saved configuration during slave configuration process */
    uart_config_s configuration_slv_CRT, configuration_slv_NXT;
    logic data_width_load, parity_mode_load, stop_bits_number_load;

        always_ff @(posedge clk_i or negedge rst_n_i) begin
            if (!rst_n_i) begin
                configuration_slv_CRT.data_width <= 2'b0;
            end else if (data_width_load) begin
                configuration_slv_CRT.data_width <= configuration_slv_NXT.data_width;
            end
        end

        always_ff @(posedge clk_i or negedge rst_n_i) begin
            if (!rst_n_i) begin
                configuration_slv_CRT.parity_mode <= 2'b0;
            end else if (parity_mode_load) begin
                configuration_slv_CRT.parity_mode <= configuration_slv_NXT.parity_mode;
            end
        end

        always_ff @(posedge clk_i or negedge rst_n_i) begin
            if (!rst_n_i) begin
                configuration_slv_CRT.stop_bits <= 2'b0;
            end else if (stop_bits_number_load) begin
                configuration_slv_CRT.stop_bits <= configuration_slv_NXT.stop_bits;
            end
        end


//-------------//
//  FSM LOGIC  //
//-------------//

    main_control_fsm_e state_CRT, state_NXT;

        always_ff @(posedge clk_i or negedge rst_n_i) begin : fsm_state_register
            if (!rst_n_i) begin 
                state_CRT <= MAIN;
            end else begin 
                state_CRT <= state_NXT;
            end
        end : fsm_state_register

    logic config_req_slv;

    assign config_req_slv = config_req_slv_i & enable_config_receive_i;

        always_comb begin : fsm_next_state_logic 

            //------------------//
            //  DEFAULT VALUES  //
            //------------------//

            /* Default next state logic */
            state_NXT = state_CRT; 
            counter_10ms_NXT = 'b0;
            config_failed_NXT = config_failed_CRT;
            config_packet_type_NXT = config_packet_type_CRT;
            syn_data_cnt_NXT = syn_data_cnt_CRT;
            configuration_slv_NXT = configuration_slv_CRT;

            /* Configuration signals */
            STR_en_o = 1'b0;
            config_o = config_i;
            config_req_mst_o = 1'b0;
            config_error_o = 1'b0;
            config_done_o = 1'b0;
            set_std_config_o = 1'b0;
            data_width_load = 1'b0;
            parity_mode_load = 1'b0;
            stop_bits_number_load = 1'b0;

            /* During configuration process, the interrupts are disabled */
            disable_global_int_o = 1'b1;

            /* FIFO signals */
            rx_fifo_read_o = 1'b0;
            tx_fifo_write_o = 1'b0;

            /* Data */
            data_tx_o = data_tx_i;

            case (state_CRT)

                /*
                 *  Set the standard configuration.
                 */
                STD_CONFIG: begin 
                    set_std_config_o = 1'b1;
                    disable_global_int_o = 1'b0;
                    state_NXT = MAIN;
                end

                /*  
                 *  In the main state the UART is controlled by the CPU, during this state the device can 
                 *  request a configuration setup or it can be requested by the other device. Standard
                 *  configuration can also be set. 
                 */ 
                MAIN: begin 
                    config_packet_type_NXT = 2'b0;
                    config_done_o = 1'b1;
                    disable_global_int_o = 1'b0;

                    rx_fifo_read_o = rx_fifo_read_i;
                    tx_fifo_write_o = tx_fifo_write_i;

                    /* If the other device requested a configuration setup (current device = SLAVE) */
                    if (config_req_slv & request_ack_i) begin 
                        state_NXT = SEND_ACKN_SLV;
                    end else if (config_req_mst_i) begin 
                        /* If the current device request a configuration setup (current device = MASTER) */
                        state_NXT = CFG_REQ_MST;
                    end 
                end

                /*
                 *  In this state, the device sends 3 SYN characters to the other device, after that
                 *  sends the configuration signal by lowering the TX line (non IDLE state) for 1ms
                 */
                CFG_REQ_MST: begin
                    /* Send 3 SYN characters */
                    if ((syn_data_cnt_CRT != SYN_NUMBER) & (!tx_fifo_full_i)) begin 
                        tx_fifo_write_o = 1'b1;
                        data_tx_o = SYN;
                        syn_data_cnt_NXT = syn_data_cnt_CRT + 1'b1;
                    end else begin
                        config_req_mst_o = 1'b1;            
                        state_NXT = (req_done_i) ? WAIT_REQ_ACKN_MST : CFG_REQ_MST;
                    end
                end

                /*
                 *  The device waits for the other device to acknowledge the configuration request. 
                 *  It needs to receive an acknowledge packet within 10ms otherwise the device will
                 *  send another request. The process repeat for three times at the most, then the 
                 *  configuration will be considered failed and the device setted with the standard
                 *  configuration. 
                 */
                WAIT_REQ_ACKN_MST: begin 
                    counter_10ms_NXT = counter_10ms_CRT + 1'b1;
                    config_req_mst_o = 1'b0;
                    syn_data_cnt_NXT = 'b0;

                    if (config_failed_CRT == 2'd3) begin 
                        /* Raise a configuration error and set the standard configuration */
                        config_error_o = 1'b1;
                        config_failed_NXT = 2'b0;
                        state_NXT = STD_CONFIG;
                    end else if (counter_10ms_CRT != COUNT_10MS) begin
                        /* Read the data when the fifo is not empty */
                        rx_fifo_read_o = !rx_fifo_empty_i;

                        if (data_rx_i == ACKN_PKT) begin 
                            state_NXT = SEND_CFG_PKT_MST;
                        end
                    end else if (counter_10ms_CRT == COUNT_10MS) begin 
                        /* Try another request */
                        config_failed_NXT = config_failed_CRT + 1'b1;
                        state_NXT = CFG_REQ_MST;
                    end
                end

                /*
                 *  The device will send a configuration packet to the slave device.
                 */
                SEND_CFG_PKT_MST: begin 
                    state_NXT = WAIT_TX_MST;
                    tx_fifo_write_o = 1'b1;

                    case (config_packet_type_CRT)
                        DW_TYPE:   data_tx_o = assemble_packet(DATA_WIDTH_ID, updated_config_i.data_width);
                        PM_TYPE:   data_tx_o = assemble_packet(PARITY_MODE_ID, updated_config_i.parity_mode);
                        SB_TYPE:   data_tx_o = assemble_packet(STOP_BITS_ID, updated_config_i.stop_bits);
                        EC_TYPE:   data_tx_o = assemble_packet(END_CONFIGURATION_ID, 2'b00);
                    endcase
                end


                /* 
                 *  Wait the transmitter to finish sending data 
                 */
                WAIT_TX_MST: begin 
                    /* Go to the next state only if the transmitter has finished sending the packet */
                    if (tx_done_i) begin
                        state_NXT = WAIT_ACKN_MST;
                    end
                end


                /*
                 *  The device is waiting for the slave acknowledgment, the fifo must be empty. 
                 *  If in 10ms the device doesn't get any acknowledgment packet, raise a configuration error.
                 *  If a non acknowledgment packet is received, it will simply be ignored.
                 */
                WAIT_ACKN_MST: begin
                    counter_10ms_NXT = counter_10ms_CRT + 1'b1;

                    /* When data arrives, read the fifo */
                    rx_fifo_read_o = !rx_fifo_empty_i;

                    /* If the packet hasn't been received in time, raise a configuration error and set
                     * standard configuration */
                    if (counter_10ms_CRT == COUNT_10MS) begin 
                        state_NXT = STD_CONFIG;
                        config_error_o = 1'b1;
                    end else if (data_rx_i == ACKN_PKT) begin
                        /* If the end configuration packet was sended go in main state */
                        if (config_packet_type_CRT == EC_TYPE) begin 
                            state_NXT = MAIN;
                            config_done_o = 1'b1;
                        end else begin 
                            state_NXT = SEND_CFG_PKT_MST; 
                        end

                        /* Go to the next configuration state */
                        config_packet_type_NXT = config_packet_type_CRT + 1'b1;
                    end 
                end   

                /*
                 *  The device waits for configuration packets. The fifo needs to be empty so other data packets
                 *  won't be considered as configuration packets. For every packet received, the device must send
                 *  an acknowlede. 
                 */
                WAIT_CFG_PKT_SLV: begin 
                    rx_fifo_read_o = !rx_fifo_empty_i;

                    /* Wait until a configuration packet arrives, then process the next configuration 
                     * packet. If there is an error in the packet received, raise a configuration error
                     * and use the standard configuration */
                    if (counter_10ms_CRT != COUNT_10MS) begin
                        if (!rx_fifo_empty_i) begin
                            config_packet_type_NXT = config_packet_type_CRT + 1'b1;
                            state_NXT = SEND_ACKN_SLV;
                        end

                        case (data_rx_i.cfg_packet.id)
                            DATA_WIDTH_ID:  begin
                                configuration_slv_NXT.data_width = data_rx_i.cfg_packet.option;
                                data_width_load = 1'b1;
                            end

                            PARITY_MODE_ID:  begin
                                configuration_slv_NXT.parity_mode = data_rx_i.cfg_packet.option;
                                parity_mode_load = 1'b1;
                            end

                            STOP_BITS_ID:  begin 
                                configuration_slv_NXT.stop_bits = data_rx_i.cfg_packet.option;
                                stop_bits_number_load = 1'b1;
                            end
                        endcase
                    end else begin 
                        state_NXT = STD_CONFIG;
                        config_error_o = 1'b1;
                    end
                end

                /*
                 *  The device will send an acknowledgment packet to continue the configuration process
                 */
                SEND_ACKN_SLV: begin           
                    /* Send acknowledge packet */
                    tx_fifo_write_o = 1'b1;
                    data_tx_o = ACKN_PKT;
                    state_NXT = WAIT_TX_SLV;
                end

                /* 
                 *  Wait transmitter to finish sending data 
                 */
                WAIT_TX_SLV: begin 
                    /* Go to the next state only if the transmitter has finished sending the packet */
                    if (tx_done_i) begin 
                        if (config_packet_type_CRT == EC_TYPE) begin 
                            /* Write the final configuration */
                            state_NXT = MAIN;
                            STR_en_o = 1'b1;
                            config_o = configuration_slv_CRT;
                        end else begin 
                            state_NXT = WAIT_CFG_PKT_SLV;
                        end
                    end
                end

            endcase
        end : fsm_next_state_logic

endmodule : control_unit

`endif