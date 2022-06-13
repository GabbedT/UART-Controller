`include "Packages/uart_pkg.sv"

module uart (
    input  logic       clk_i,
    input  logic       rst_n_i,
    input  logic       chip_sel_n_i,
    input  logic [2:0] address_i,
    input  logic       read_write_i,
    inout  logic [7:0] data_io,
    input  logic       rx_i,
    input  logic       iack_i,

    output logic       tx_o,
    output logic       ireq_n_o    
);

    /* Reset is an asyncronous signal, thus it must be passed through a syncronizer */
    logic rst_ff, rst_sync;

    always_ff @(posedge clk_i or negedge rst_n_i) begin : reset_syncronizer
        if (!rst_n_i) begin
            {rst_sync, rst_ff} <= 2'b0;
        end else begin
            {rst_sync, rst_ff} <= {rst_ff, 1'b1};
        end
    end : reset_syncronizer


//---------------------//
//  POSEDGE DETECTORS  //
//---------------------//

    /* Gated with chip select */
    logic read_cs, write_cs;

    /* Read is active high */
    assign read_cs = read_write_i & !chip_sel_n_i;

    /* Write is active low */
    assign write_cs = !(read_write_i | chip_sel_n_i);

    /* Read and write signal must stay low for only 1 clock cycle */
    logic read, write;

    edge_detector #(1) posedge_read_det (
        .clk_i        ( clk_i   ),
        .signal_i     ( read_cs ),
        .edge_pulse_o ( read    )
    );

    edge_detector #(1) posedge_write_det (
        .clk_i        ( clk_i    ),
        .signal_i     ( write_cs ),
        .edge_pulse_o ( write    )
    );


    logic int_ack;

    edge_detector #(1) posedge_ackn_det (
        .clk_i        ( clk_i   ),
        .signal_i     ( iack_i  ),
        .edge_pulse_o ( int_ack )   
    );


//-----------------------//
//  BAUD RATE GENERATOR  //
//-----------------------//

    logic [15:0] divisor;
    logic        baud_rate_tick;
    logic        reset_bd_n, reset_bd_gen;

    assign reset_bd_n = !reset_bd_gen & rst_sync;

    baud_rate_generator baud_rate_gen (
        .clk_i        ( clk_i          ),
        .rst_n_i      ( reset_bd_n     ),
        .divisor_i    ( divisor        ),
        .ov_baud_rt_o ( baud_rate_tick )
    );


//-------------------//
//  MAIN CONTROLLER  //
//-------------------//

    logic [7:0]   data_rx, data_TXR;
    logic         tx_done, req_done;
    logic         parity;
    logic         rx_fifo_empty, rx_fifo_read, tx_fifo_write, tx_fifo_full;
    logic         config_request_acknowledged;
    logic         enable_configuration;
    logic         configuration_received, send_configuration;
    uart_config_s current_configuration, next_configuration, configuration_out;
    logic         disable_global_interrupt;
    logic         enable_STR;
    logic         start_configuration;
    logic         set_std_configuration;
    logic         configuration_done;
    logic         rx_read, tx_write;
    logic [7:0]   data_tx;
    logic         configuration_error, parity_error;

    control_unit controller (
        .clk_i                   ( clk_i                       ),
        .rst_n_i                 ( rst_sync                    ),
        .data_rx_i               ( data_rx                     ),
        .data_tx_i               ( data_TXR                    ),
        .tx_done_i               ( tx_done                     ),
        .req_done_i              ( req_done                    ),
        .parity_i                ( parity                      ),
        .rx_fifo_empty_i         ( rx_fifo_empty               ),
        .rx_fifo_read_i          ( rx_read                     ),
        .tx_fifo_write_i         ( tx_write                    ),
        .tx_fifo_full_i          ( tx_fifo_full                ),
        .request_ack_i           ( config_request_acknowledged ),
        .enable_config_receive_i ( enable_configuration        ),
        .config_req_slv_i        ( configuration_received      ),
        .config_req_mst_i        ( send_configuration          ),
        .config_i                ( current_configuration       ),
        .updated_config_i        ( next_configuration          ),
        .disable_global_int_o    ( disable_global_interrupt    ),
        .STR_en_o                ( enable_STR                  ),
        .config_o                ( configuration_out           ),
        .config_req_mst_o        ( start_configuration         ),
        .set_std_config_o        ( set_std_configuration       ),
        .config_done_o           ( configuration_done          ),
        .rx_fifo_read_o          ( rx_fifo_read                ),
        .tx_fifo_write_o         ( tx_fifo_write               ),
        .data_tx_o               ( data_tx                     ),
        .config_error_o          ( configuration_error         ),
        .parity_error_o          ( parity_error                )
    );


//---------------//
//  TRANSMITTER  //
//---------------//

    logic  tx_enable;
    logic  tx_data_stream_mode;
    logic  tx_idle;

    transmitter tx (
        .clk_i                 ( clk_i                             ),
        .rst_n_i               ( rst_sync                          ),
        .enable                ( tx_enable                         ),
        .ov_baud_rt_i          ( baud_rate_tick                    ),
        .data_tx_i             ( data_tx                           ),
        .tx_fifo_write_i       ( tx_fifo_write                     ),
        .config_req_mst_i      ( start_configuration               ),
        .config_req_slv_i      ( configuration_received            ),
        .tx_data_stream_mode_i ( tx_data_stream_mode               ),
        .data_width_i          ( current_configuration.data_width  ),
        .stop_bits_number_i    ( current_configuration.stop_bits   ),
        .parity_mode_i         ( current_configuration.parity_mode ),
        .tx_o                  ( tx_o                              ),
        .tx_done_o             ( tx_done                           ),
        .req_done_o            ( req_done                          ),
        .tx_fifo_full_o        ( tx_fifo_full                      ),
        .tx_idle_o             ( tx_idle                           )
    );


//------------//
//  RECEIVER  //
//------------//

    logic       rx_enable;
    logic [5:0] threshold;
    logic       rx_data_stream_mode;
    logic       rx_fifo_full;
    logic       overrun_error;
    logic       frame_error;
    logic       data_rx_ready;
    logic       rx_idle;

    receiver rx (
        .clk_i                 ( clk_i                             ),
        .rst_n_i               ( rst_sync                          ),
        .enable                ( rx_enable                         ),
        .ov_baud_rt_i          ( baud_rate_tick                    ),
        .rx_i                  ( rx_i                              ),
        .rx_fifo_read_i        ( rx_fifo_read                      ),
        .req_ackn_i            ( config_request_acknowledged       ),
        .threshold_i           ( threshold                         ),
        .rx_data_stream_mode_i ( rx_data_stream_mode               ),
        .data_width_i          ( current_configuration.data_width  ),
        .stop_bits_number_i    ( current_configuration.stop_bits   ),
        .parity_mode_i         ( current_configuration.parity_mode ),
        .rx_fifo_full_o        ( rx_fifo_full                      ),
        .rx_fifo_empty_o       ( rx_fifo_empty                     ),
        .config_req_slv_o      ( configuration_received            ),
        .overrun_error_o       ( overrun_error                     ),
        .frame_error_o         ( frame_error                       ),
        .parity_o              ( parity                            ),
        .rx_data_ready_o       ( data_rx_ready                     ),
        .data_rx_o             ( data_rx                           ),
        .rx_idle_o             ( rx_idle                           )  
    );


//---------------------//
//  INTERRUPT ARBITER  //
//---------------------//

    logic [2:0] interrupt_vector;
    logic       tx_done_interrupt_enable;
    logic       store_interrupt_vector;
    logic       overrun_error_interrupt_enable;
    logic       frame_error_interrupt_enable;
    logic       parity_error_interrupt_enable;
    logic       data_rx_ready_interrupt_enable;
    logic       interrupt_request;

    interrupt_arbiter arbiter (
        .clk_i                 ( clk_i                          ),
        .rst_n_i               ( rst_sync                       ),
        .rx_dsm_i              ( rx_data_stream_mode            ),
        .rx_rdy_i              ( data_rx_ready                  ),
        .tx_done_i             ( tx_done                        ),
        .disable_interrupts_i  ( disable_global_interrupt       ),
        .config_error_i        ( configuration_error            ),
        .parity_error_i        ( parity_error                   ),
        .frame_error_i         ( frame_error                    ),
        .overrun_error_i       ( overrun_error                  ),
        .rx_fifo_full_i        ( rx_fifo_full                   ),
        .config_req_slv_i      ( configuration_received         ),
        .tx_done_en_i          ( tx_done_interrupt_enable       ),
        .overrun_error_en_i    ( overrun_error_interrupt_enable ),
        .frame_error_en_i      ( frame_error_interrupt_enable   ),
        .parity_error_en_i     ( parity_error_interrupt_enable  ),
        .rx_rdy_en_i           ( data_rx_ready_interrupt_enable ),
        .int_ackn_i            ( int_ack                        ),
        .read_rx_data_i        ( rx_fifo_read                   ),
        .rx_fifo_empty_i       ( rx_fifo_empty                  ),
        .interrupt_vector_o    ( interrupt_vector               ),
        .store_int_vect_o      ( store_interrupt_vector         ),
        .ireq_n_o              ( interrupt_request              )
    );

    assign ireq_n_o = interrupt_request;


//-------------//
//  REGISTERS  //
//-------------//

    configuration_registers config_registers (
        .clk_i                    ( clk_i                             ),
        .rst_n_i                  ( rst_sync                          ),
        .read_i                   ( read                              ),
        .write_i                  ( write                             ),
        .address_i                ( address_i                         ),
        .data_io                  ( data_io                           ),
        .tx_enable_o              ( tx_enable                         ),
        .rx_enable_o              ( rx_enable                         ),
        .int_ackn_i               ( int_ack                           ),
        .req_ackn_o               ( config_request_acknowledged       ),
        .tx_done_en_o             ( tx_done_interrupt_enable          ),
        .STR_en_i                 ( enable_STR                        ),
        .set_std_config_i         ( set_std_configuration             ),
        .data_width_i             ( configuration_out.data_width      ),
        .parity_mode_i            ( configuration_out.parity_mode     ),
        .stop_bits_i              ( configuration_out.stop_bits       ),
        .tx_dsm_o                 ( tx_data_stream_mode               ),
        .rx_dsm_o                 ( rx_data_stream_mode               ),
        .data_width_o             ( current_configuration.data_width  ),
        .parity_mode_o            ( current_configuration.parity_mode ),
        .stop_bits_o              ( current_configuration.stop_bits   ),
        .updated_data_width_o     ( next_configuration.data_width     ),
        .updated_parity_mode_o    ( next_configuration.parity_mode    ),
        .updated_stop_bits_o      ( next_configuration.stop_bits      ),
        .tx_idle_i                ( tx_idle                           ),
        .rx_idle_i                ( rx_idle                           ),
        .divisor_o                ( divisor                           ),
        .reset_bd_gen_o           ( reset_bd_gen                      ),
        .tx_fifo_full_i           ( tx_fifo_full                      ),
        .rx_fifo_empty_i          ( rx_fifo_empty                     ),
        .rx_fifo_threshold_o      ( threshold                         ),
        .configuration_done_i     ( configuration_done                ),
        .int_pending_i            ( interrupt_request                 ),
        .enable_configuration_o   ( enable_configuration              ),
        .send_configuration_req_o ( send_configuration                ),
        .interrupt_vector_i       ( interrupt_vector                  ),
        .interrupt_vector_en_i    ( store_interrupt_vector            ),
        .rx_rdy_en_o              ( data_rx_ready_interrupt_enable    ),
        .frame_error_en_o         ( frame_error_interrupt_enable      ),
        .parity_error_en_o        ( parity_error_interrupt_enable     ),
        .overrun_error_en_o       ( overrun_error_interrupt_enable    ),
        .rx_data_i                ( data_rx                           ),
        .rx_fifo_read_o           ( rx_read                           ),
        .tx_data_o                ( data_TXR                          ),
        .tx_fifo_write_o          ( tx_write                          )
    );

endmodule : uart