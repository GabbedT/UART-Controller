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

import UART_pkg::*;
import main_controller_pkg::*;
import fsm_pkg::*;

module main_controller ( 
    input  logic         rst_n_i,
    input  logic         clk_i,
    input  logic         interrupt_ackn_i,
    /* Data */
    input  data_packet_u data_rx_i,
    input  logic [7:0]   data_tx_i,
    /* Transmitter */
    input  logic         tx_done_i,
    input  logic         req_done_i,
    /* Error detection */
    input  logic         parity_i,    
    /* FIFO status */ 
    input  logic         rx_fifo_empty_i,
    input  logic         tx_fifo_empty_i,
    input  logic         rx_fifo_read_i,
    input  logic         tx_fifo_write_i,
    /* Configuration */
    input  logic [1:0]   communication_mode_i,
    input  logic         enable_config_receive_i,
    input  logic         config_req_slv_i,
    input  logic         config_req_mst_i,
    input  logic         set_std_config_i,
    input  uart_config_s config_i,
    input  uart_config_s updated_config_i,
    input  logic         rx_data_stream_mode_i,
    input  logic         tx_data_stream_mode_i,
    input  logic         req_ackn_i,

    output logic         STR_en_o,
    output uart_config_s config_o,
    output logic         config_req_mst_o,
    output logic         set_std_config_o,
    output logic         rx_data_stream_mode_o,
    output logic         tx_data_stream_mode_o,
    output logic [1:0]   communication_mode_o,
    output logic         config_done_o,
    output logic         req_ackn_o,
    output logic         tx_enable_o,
    output logic         rx_enable_o,
    /* FIFO operations */
    output logic         rx_fifo_read_o,
    output logic         tx_fifo_write_o,
    /* Data */
    output logic [7:0]   data_tx_o,
    /* Error */
    output logic         config_error_o,
    output logic         parity_error_o
);

    /* How many clock cycles does it need to reach 10 ms  
     * based on a specific system clock */
    localparam COUNT_10MS = SYSTEM_CLOCK_FREQ / 100;


//------------//
//  DATAPATH  //
//------------//

    /* Counter to 50ms */
    logic [$clog2(COUNT_10MS) - 1:0] counter_50ms[NXT:CRT];

        always_ff @(posedge clk_i) begin : ms50_counter
            if (!rst_n_i) begin   
                counter_50ms[CRT] <= 'b0;
            end else if (counter_50ms[CRT] == COUNT_10MS) begin  
                counter_50ms[CRT] <= 'b0;
            end else begin
                counter_50ms[CRT] <= counter_50ms[NXT];
            end
        end : ms50_counter


    /* Number of times the configuration failed */
    logic [1:0] config_failed[NXT:CRT];

    /* Tracks the state of the configuration */
    logic [1:0] config_packet_type[NXT:CRT];

    localparam DW_TYPE = 2'b00;  /* Data width        */
    localparam PM_TYPE = 2'b01;  /* Parity mode       */
    localparam SB_TYPE = 2'b10;  /* Stop bits         */
    localparam EC_TYPE = 2'b11;  /* End configuration */

    /* Count the number of SYN character sended */
    logic [$clog2(SYN_NUMBER) - 1:0] syn_data_cnt[NXT:CRT];  
    
        /* Count the number of times the device has tried to reques a configuration
         * and the slave device didn't respond (max 3 times) */
        always_ff @(posedge clk_i) begin : datapath_register
            if (!rst_n_i) begin 
                config_failed[CRT] <= 'b0;
                config_packet_type[CRT] <= 'b0;
                syn_data_cnt[CRT] <= 2'b0;
            end else begin 
                config_failed[CRT] <= config_failed[NXT];
                config_packet_type[CRT] <= config_packet_type[NXT];
                syn_data_cnt[CRT] <= syn_data_cnt[NXT];
            end
        end : datapath_register


//-------------//
//  FSM LOGIC  //
//-------------//

    fsm_pkg::main_control_fsm_e state[NXT:CRT];

        always_ff @(posedge clk_i) begin : fsm_state_register
            if (!rst_n_i) begin 
                state[CRT] <= MAIN;
            end else begin 
                state[CRT] <= state[NXT];
            end
        end : fsm_state_register

    logic config_req_slv;

    assign config_req_slv = config_req_slv_i & enable_config_receive_i;

        always_comb begin : fsm_next_state_logic 

            //------------------//
            //  DEFAULT VALUES  //
            //------------------//

            /* Default next state logic */
            state[NXT] = state[CRT]; 
            counter_50ms[NXT] = 'b0;
            config_failed[NXT] = 'b0;
            config_packet_type[NXT] = config_packet_type[CRT];
            syn_data_cnt[NXT] = 'b0;

            /* Configuration signals */
            STR_en_o = 1'b0;
            config_o = config_i;
            config_req_mst_o = 1'b0;
            rx_data_stream_mode_o = rx_data_stream_mode_i;
            tx_data_stream_mode_o = tx_data_stream_mode_i;
            communication_mode_o = communication_mode_i;
            config_error_o = 1'b0;
            config_done_o = 1'b0;
            set_std_config_o = 1'b0;

            /* FIFO signals */
            rx_fifo_read_o = 1'b0;
            tx_fifo_write_o = 1'b0;

            /* Data */
            data_tx_o = data_tx_i;

            case (state[CRT])

            /*
             *  Setup the standard configuration.
             */
            STD_CONFIG: begin 
                STR_en_o = 1'b1;
                set_std_config_o = 1'b1;
                rx_data_stream_mode_o = 1'b0;
                tx_data_stream_mode_o = 1'b0;
                communication_mode_o = STD_COMM_MODE;

                state[NXT] = MAIN;
            end

            /*  
             *  In the main state the UART is controlled by the CPU, during this state the device can 
             *  request a configuration setup or it can be requested by the other device. Standard
             *  configuration can also be set. 
             */ 
            MAIN: begin 
                config_packet_type[NXT] = 'b0;
                config_done_o = 1'b1;

                rx_fifo_read_o = rx_fifo_read_i;
                tx_fifo_write_o = tx_fifo_write_i;

                /* If the other device requested a configuration setup (current device = SLAVE) */
                if (config_req_slv & req_ackn_i) begin 
                    state[NXT] = SEND_ACKN_SLV;
                end else if (config_req_mst_i) begin 
                    /* If the current device request a configuration setup (current device = MASTER) */
                    state[NXT] = CFG_REQ_MST;
                end else if (set_std_config_i) begin 
                    state[NXT] = STD_CONFIG; 
                end 
            end

            /*
             *  This state just send a configuration request to the transmitter which will set
             *  the TX line to a non IDLE state for 10ms. Go to the next stage only if the 
             *  transmitter has finished requesting.
             */
            CFG_REQ_MST: begin
                /* Send 3 SYN characters */
                if (syn_data_cnt[CRT] != SYN_NUMBER) begin 
                    tx_fifo_write_o = 1'b1;
                    data_tx_o = SYN;
                    syn_data_cnt[NXT] = syn_data_cnt[CRT] + 1'b1;
                end else begin
                    config_req_mst_o = 1'b1;

                    if (req_done_i) begin
                        tx_fifo_write_o = 1'b1;
                        data_tx_o = SYN;                
                        state[NXT] = (tx_done_i) ? WAIT_REQ_ACKN_MST : CFG_REQ_MST;
                    end
                end
            end

            /*
             *  The device waits for the other device to acknowledge the configuration request. 
             *  It needs to receive an acknowledgement packet within 50ms otherwise the device will
             *  send another request. The process repeat for three times at the most, then the 
             *  configuration will be considered failed and the device setted with the standard
             *  configuration. 
             */
            WAIT_REQ_ACKN_MST: begin 
                counter_50ms[NXT] = counter_50ms[CRT] + 1'b1;
                config_req_mst_o = 1'b0;

                if (config_failed[CRT] == 2'd3) begin 
                    /* Raise a configuration error and set the standard configuration */
                    config_error_o = 1'b1;
                    config_failed[NXT] = 2'b0;
                    state[NXT] = STD_CONFIG;
                end else if (counter_50ms[CRT] != COUNT_10MS) begin
                    /* Read the data when the fifo is not empty */
                    rx_fifo_read_o = !rx_fifo_empty_i;

                    if ((config_packet_type[CRT] == EC_TYPE) & (data_rx_i == ACKN_PKT)) begin 
                        state[NXT] = MAIN;
                    end else if (data_rx_i == ACKN_PKT) begin 
                        state[NXT] = SETUP_MST;
                    end
                end else if (counter_50ms[CRT] == COUNT_10MS) begin 
                    /* Try another request */
                    config_failed[NXT] = config_failed[CRT] + 1'b1;
                    state[NXT] = CFG_REQ_MST;
                end
            end

            /*
             *  The device will send a configuration packet to the slave device.
             */
            SETUP_MST: begin 
                state[NXT] = WAIT_TX_MST;
                tx_fifo_write_o = 1'b1;

                case (config_packet_type[CRT])
                    DW_TYPE:   data_tx_o = assemble_packet(DATA_WIDTH_ID, updated_config_i.data_width);
                    PM_TYPE:   data_tx_o = assemble_packet(PARITY_MODE_ID, updated_config_i.parity_mode);
                    SB_TYPE:   data_tx_o = assemble_packet(STOP_BITS_ID, updated_config_i.stop_bits);
                    EC_TYPE:   data_tx_o = assemble_packet(END_CONFIGURATION_ID, 2'b00);
                endcase
            end


            /* 
             *  Wait transmitter to finsish sending data 
             */
            WAIT_TX_MST: begin 
                /* Go to the next state only if the transmitter has finished sending the packet */
                if (tx_done_i) begin
                    state[NXT] = WAIT_ACKN_MST;
                end
            end


            /*
             *  The device is waiting for the slave acknowledgment, the fifo must be empty. 
             *  Enable data stream mode so the device doesn't interrupt everytime it receive a packet.
             *  If in 50ms the device doesn't get any acknowledgment packet, raise a configuration error.
             *  If a non acknowledgment packet is received, it will simply be ignored.
             */
            WAIT_ACKN_MST: begin
                counter_50ms[NXT] = counter_50ms[CRT] + 1'b1;
                rx_data_stream_mode_o = 1'b1;

                /* When data arrives, read the fifo */
                rx_fifo_read_o = !rx_fifo_empty_i;

                /* If the packet hasn't been received in time, raise a configuration error and set
                 * standard configuration */
                if (counter_50ms[CRT] == COUNT_10MS) begin 
                    state[NXT] = STD_CONFIG;
                    config_error_o = 1'b1;
                end else if (data_rx_i == ACKN_PKT) begin
                    /* If the end configuration packet was sended go in main state */
                    if (config_packet_type[CRT] == EC_TYPE) begin 
                        state[NXT] = MAIN;
                    end else begin 
                        state[NXT] = SETUP_MST; 
                    end

                    /* Go to the next configuration state */
                    config_packet_type[NXT] = config_packet_type[CRT] + 1'b1;
                end 
            end   

            /*
             *  The device waits for configuration packets. The fifo's needs to be empty so other data packets
             *  won't be considered as configuration packets. For every packet received, the device must send
             *  an acknowledgment. If there is a configuration request from the master device, the slave must
             *  enable data stream mode so during the configuration the device doesn't interrupt everytime it 
             *  receive a packet.
             */
            SETUP_SLV: begin 
                rx_data_stream_mode_o = 1'b1;

                rx_fifo_read_o = !rx_fifo_empty_i;

                /* Wait until a configuration packet arrives, then process the next configuration 
                * packet. If there is an error in the packet received, raise a configuration error
                * and use the standard configuration */
                if (counter_50ms[CRT] != COUNT_10MS) begin
                    if (!rx_fifo_empty_i) begin
                        config_packet_type[NXT] = config_packet_type[CRT] + 1'b1;
                        state[NXT] = SEND_ACKN_SLV;
                        STR_en_o = 1'b1;
                    end

                    case (data_rx_i.cfg_packet.id)
                        DATA_WIDTH_ID:  config_o.data_width = data_rx_i.cfg_packet.option;
                        PARITY_MODE_ID: config_o.parity_mode = data_rx_i.cfg_packet.option;
                        STOP_BITS_ID:   config_o.stop_bits = data_rx_i.cfg_packet.option;
                    endcase
                end else begin 
                    state[NXT] = STD_CONFIG;
                    config_error_o = 1'b1;
                end
            end

            /*
             *  The device will send an acknowledgment packet to continue the configuration process
             */
            SEND_ACKN_SLV: begin           
                /* Send ackowledge packet */
                tx_fifo_write_o = 1'b1;
                data_tx_o = ACKN_PKT;
                state[NXT] = WAIT_TX_SLV;
            end

            /* 
             *  Wait transmitter to finsish sending data 
             */
            WAIT_TX_SLV: begin 
                /* Go to the next state only if the transmitter has finished sending the packet */
                if (tx_done_i) begin 
                    if (config_packet_type[CRT] == EC_TYPE) begin 
                        state[NXT] = MAIN;
                    end else begin 
                        state[NXT] = SETUP_SLV;
                    end
                end
            end

        endcase
      end : fsm_next_state_logic


//-------------------------//
//  ERROR DETECTION LOGIC  //
//-------------------------//

    logic parity, parity_error;

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

            /* Select ODD or EVEN parity */
            case (config_i.parity_mode)
                EVEN:    parity_error = parity_i != (parity ^ 1'b0);
                ODD:     parity_error = parity_i != (parity ^ 1'b1);
                default: parity_error = 1'b0;
            endcase
        end : parity_detection_logic

    /* Detect parity error positive edge for interrupt arbiter */
    edge_detector #(1) posedge_detector (
        .clk_i        ( clk_i                ),
        .signal_i     ( parity_error         ),
        .edge_pulse_o ( parity_error_o       )
    );


//---------------------//
//  COMMUNICATION MODE //
//---------------------//

    assign tx_enable_o = communication_mode_i[0];
    assign rx_enable_o = communication_mode_i[1];


//--------------//
//  ASSERTIONS  //
//--------------//

    /* Check that no operation is done during reset */
    sequence no_operation;
    !(tx_fifo_write_o & rx_fifo_read_o & STR_en_o & config_done_o & config_req_mst_o);
    endsequence : no_operation

    /* Check the sequence, since the reset is syncronous the FSM needs 1 clock cycle to reach the desired state */
    property rst_values;
    @(posedge clk_i) !rst_n_i |=> no_operation;
    endproperty : rst_values

    /* Check that after failing three times to receive an acknowledgment, the device in the next clock cycle set 
    * the standard configuration and then goes into main state */
    property fail_req_ackn;
    @(posedge clk_i) disable iff (!rst_n_i)
    (state[CRT] == WAIT_REQ_ACKN_MST) && (config_failed[CRT] == 2'd3) |=> (config_o == STD_CONFIGURATION) ##1 (state[CRT] == MAIN);
    endproperty : fail_req_ackn

    /* Check that the acknowledgement packet arrives in time */
    property ackn_timing;
    @(posedge clk_i) disable iff (!rst_n_i)
    (state[CRT] == WAIT_REQ_ACKN_MST) && (!rx_fifo_empty_i) |-> ((counter_50ms[CRT] < COUNT_10MS) && (data_rx_i == ACKN_PKT));
    endproperty : ackn_timing

    /* Configuration request signals must not be asserted when not in main state */
    property cfg_req_chk;
    @(posedge clk_i) (state[CRT] != MAIN) |-> !config_req_mst_i & !config_req_slv_i;
    endproperty : cfg_req_chk

    /* In wait acknowledgement state the receiver fifo has to be empty */ 
    property rx_fifo_chk;
    @(posedge clk_i) $rose(state[CRT] == WAIT_REQ_ACKN_MST) || $rose(state[CRT] == WAIT_ACKN_MST) |-> rx_fifo_empty_i; 
    endproperty : rx_fifo_chk

    /* When the device is sending the acknowledgement, the fifo has to be empty */
    property tx_fifo_chk;
    @(posedge clk_i) $rose(state[CRT] == SETUP_SLV) |-> tx_fifo_empty_i;
    endproperty

    /* The UART can't write and read the fifos at the same time */
    property fifos_op_chk;
    @(posedge clk_i) disable iff (!rst_n_i) 
    rx_fifo_read_i != tx_fifo_write_i;
    endproperty

    /* Parity error should be high for only one clock cycle */
    property parity_error_chk;
    @(posedge clk_i) parity_error |=> parity_error_o ##1 !parity_error_o;
    endproperty

    initial begin : assertions
        assert property (rst_values)
        else $info("[Main controller] The device must not do any operation during reset!");
        
        assert property (fail_req_ackn)
        else $info("[Main controller] Failed recovery from missing request acknowledgment!");
        
        assert property (ackn_timing)
        else $info("[Main controller] Illegal acknowledgement packet timing");
        
        assert property (cfg_req_chk)
        else $info("[Main controller] During the configuration the device can't send or receive any configuration request!");
        
        assert property (rx_fifo_chk)
        else $info("[Main controller] Receiver fifo is not empty!");
        
        assert property (tx_fifo_chk)
        else $info("[Main controller] Transmitter fifo is not empty!");
        
        assert property (fifos_op_chk)
        else $info("[Main controller] The device can't send and read data in the same clock cycle!");

        assert property (parity_error_chk)
        else $info("[Main controller] Fail on parity error!");
    end : assertions

endmodule : main_controller