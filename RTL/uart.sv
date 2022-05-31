import main_controller_pkg::*;

module uart (
    input  logic       clk_i,
    input  logic       rst_n_i,
    input  logic       chip_sel_n_i,
    input  logic [2:0] address_i,
    input  logic       read_write_i,
    inout  logic [7:0] data_io,
    input  logic       rx_i,

    output logic       tx_o,
    output logic       ireq_n_o
);

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


//-----------------------//
//  BAUD RATE GENERATOR  //
//-----------------------//

    logic [15:0] divisor;
    logic        baud_rate_tick;
    logic        reset_bd_n, reset_bd_gen;

    assign reset_bd_n = !reset_bd_gen & rst_n_i;

    baud_rate_generator baud_rate_gen (
        .clk_i        ( clk_i          ),
        .rst_n_i      ( reset_bd_n     ),
        .divisor_i    ( divisor        ),
        .ov_baud_rt_o ( baud_rate_tick )
    );


//-------------------//
//  MAIN CONTROLLER  //
//-------------------//

    logic         interrupt_ackn;
    logic         parity;
    logic [1:0]   communication_mode_i, communication_mode_o;
    logic         enable_config_receive;
    logic         config_req_slv;
    logic         config_req_mst_i, config_req_mst_o;
    logic         set_std_config_i; 
    uart_config_s config_i, config_o, updated_config_i;
    logic         req_ackn;
    logic         config_done;
    logic         config_error;
    logic         parity_error;
    logic         STR_en;
    logic         set_std_config;


    /* Receiver signals */
    logic [7:0] data_rx; 
    logic       rx_fifo_empty;
    logic       rx_fifo_read_i, rx_fifo_read_o;
    logic       rx_data_stream_mode_i, rx_data_stream_mode_o;
    logic       rx_enable;

    /* Transmitter signals */
    logic [7:0] data_tx_i, data_tx_o;
    logic       tx_done;
    logic       req_done;
    logic       tx_fifo_empty;
    logic       tx_fifo_write_i, tx_fifo_write_o;
    logic       tx_data_stream_mode_i, tx_data_stream_mode_o;
    logic       tx_enable;

    main_controller main_controller_unit (
        .rst_n_i                 ( rst_n_i               ),
        .clk_i                   ( clk_i                 ),
        .interrupt_ackn_i        ( interrupt_ackn        ),
        .data_rx_i               ( data_rx               ),
        .data_tx_i               ( data_tx_i             ),
        .tx_done_i               ( tx_done               ),
        .req_done_i              ( req_done              ),
        .parity_i                ( parity                ),
        .rx_fifo_empty_i         ( rx_fifo_empty         ),
        .tx_fifo_empty_i         ( tx_fifo_empty         ),
        .rx_fifo_read_i          ( rx_fifo_read_i        ),
        .tx_fifo_write_i         ( tx_fifo_write_i       ),
        .communication_mode_i    ( communication_mode_i  ),
        .enable_config_receive_i ( enable_config_receive ),
        .config_req_slv_i        ( config_req_slv        ),
        .config_req_mst_i        ( config_req_mst_i      ),
        .set_std_config_i        ( set_std_config_i      ),
        .config_i                ( config_i              ),
        .updated_config_i        ( updated_config_i      ),
        .rx_data_stream_mode_i   ( rx_data_stream_mode_i ),
        .tx_data_stream_mode_i   ( tx_data_stream_mode_i ),
        .req_ackn_i              ( req_ackn              ),
        .STR_en_o                ( STR_en                ),
        .config_o                ( config_o              ),
        .config_req_mst_o        ( config_req_mst_o      ),
        .set_std_config_o        ( set_std_config        ),
        .rx_data_stream_mode_o   ( rx_data_stream_mode_o ),
        .tx_data_stream_mode_o   ( tx_data_stream_mode_o ),
        .communication_mode_o    ( communication_mode_o  ),
        .config_done_o           ( config_done           ),
        .tx_enable_o             ( tx_enable             ),
        .rx_enable_o             ( rx_enable             ),
        .rx_fifo_read_o          ( rx_fifo_read_o        ),
        .tx_fifo_write_o         ( tx_fifo_write_o       ),
        .data_tx_o               ( data_tx_o             ),
        .config_error_o          ( config_error          ),
        .parity_error_o          ( parity_error          )
    );


//---------------//
//  TRANSMITTER  //
//---------------//

    logic [1:0] data_width, stop_bits, parity_mode;
    logic tx_fifo_full;
    logic tx_idle;

    assign config_i.data_width = data_width;
    assign config_i.stop_bits = stop_bits;
    assign config_i.parity_mode = parity_mode;

    transmitter tx (
        .clk_i                 ( clk_i                 ),
        .rst_n_i               ( rst_n_i               ),
        .enable                ( tx_enable             ),
        .ov_baud_rt_i          ( baud_rate_tick        ),
        .data_tx_i             ( data_tx_o             ),
        .tx_fifo_write_i       ( tx_fifo_write_o       ),
        .config_req_mst_i      ( config_req_mst_o      ),
        .config_req_slv_i      ( config_req_slv        ),
        .tx_data_stream_mode_i ( tx_data_stream_mode_o ),
        .data_width_i          ( data_width            ),
        .stop_bits_number_i    ( stop_bits             ),
        .parity_mode_i         ( parity_mode           ),
        .tx_o                  ( tx_o                  ),
        .tx_done_o             ( tx_done               ),
        .req_done_o            ( req_done              ),
        .tx_fifo_empty_o       ( tx_fifo_empty         ),
        .tx_fifo_full_o        ( tx_fifo_full          ),
        .tx_idle_o             ( tx_idle               )
    );


//------------//
//  RECEIVER  //
//------------//

    logic [5:0] threshold;
    logic       rx_fifo_full;
    logic       overrun_error;
    logic       frame_error;
    logic       rxd_rdy;
    logic       rx_idle;

    receiver rx (
        .clk_i                 ( clk_i                 ),
        .rst_n_i               ( rst_n_i               ),
        .enable                ( rx_enable             ),
        .ov_baud_rt_i          ( baud_rate_tick        ),
        .rx_i                  ( rx_i                  ),
        .rx_fifo_read_i        ( rx_fifo_read_o        ),
        .req_ackn_i            ( req_ackn              ),
        .threshold_i           ( threshold             ),
        .rx_data_stream_mode_i ( rx_data_stream_mode_o ),
        .data_width_i          ( data_width            ),
        .stop_bits_number_i    ( stop_bits             ),
        .parity_mode_i         ( parity_mode           ),
        .rx_fifo_full_o        ( rx_fifo_full          ),
        .rx_fifo_empty_o       ( rx_fifo_empty         ),
        .config_req_slv_o      ( config_req_slv        ),
        .overrun_error_o       ( overrun_error         ),
        .frame_error_o         ( frame_error           ),
        .parity_o              ( parity                ),
        .rx_done_o             ( rx_done               ),
        .rxd_rdy_o             ( rxd_rdy               ),
        .data_rx_o             ( data_rx               ),
        .rx_idle_o             ( rx_idle               )
    );


//---------------------//
//  INTERRUPT ARBITER  //
//---------------------//

    logic       overrun_error_en;
    logic       frame_error_en;
    logic       parity_error_en;
    logic       rx_rdy_en;
    logic       int_ackn;
    logic [2:0] interrupt_id;
    logic       enable_int_id;
    logic       int_pending;

    interrupt_arbiter arbiter (
        .clk_i                 ( clk_i                 ),
        .rst_n_i               ( rst_n_i               ),
        .rx_dsm_i              ( rx_data_stream_mode_o ),
        .rx_rdy_i              ( rxd_rdy               ),
        .tx_done_i             ( tx_done               ),
        .config_error_i        ( config_error          ),
        .parity_error_i        ( parity_error          ),
        .frame_error_i         ( frame_error           ),
        .overrun_error_i       ( overrun_error         ),
        .rx_fifo_full_i        ( rx_fifo_full          ),
        .config_req_slv_i      ( config_req_slv        ),
        .overrun_error_en_i    ( overrun_error_en      ),
        .frame_error_en_i      ( frame_error_en        ),
        .parity_error_en_i     ( parity_error_en       ),
        .rx_rdy_en_i           ( rx_rdy_en             ),
        .int_ackn_i            ( int_ackn              ),
        .config_ackn_i         ( req_ackn              ),
        .read_rx_data_i        ( rx_fifo_read_i        ),
        .rx_fifo_empty_i       ( rx_fifo_empty         ),
        .interrupt_vector_o    ( interrupt_id          ),
        .enable_int_vec_o      ( enable_int_id         ),
        .ireq_n_o              ( int_pending           )
    );

    assign ireq_n_o = int_pending;


//-------------//
//  REGISTERS  //
//-------------//

    configuration_registers config_registers (
        .clk_i                   ( clk_i                        ),
        .rst_n_i                 ( rst_n_i                      ),
        .read_i                  ( read                         ),
        .write_i                 ( write                        ),
        .address_i               ( address_i                    ),
        .data_io                 ( data_io                      ),
        .STR_en_i                ( STR_en                       ),
        .set_std_config_i        ( set_std_config               ),
        .data_width_i            ( config_o.data_width          ),
        .parity_mode_i           ( config_o.parity_mode         ),
        .stop_bits_i             ( config_o.stop_bits           ),
        .tx_dsm_o                ( tx_data_stream_mode_i        ),
        .rx_dsm_o                ( rx_data_stream_mode_i        ),
        .data_width_o            ( data_width                   ),
        .parity_mode_o           ( parity_mode                  ),
        .stop_bits_o             ( stop_bits                    ),
        .updated_data_width_o    ( updated_config_i.data_width  ),
        .updated_parity_mode_o   ( updated_config_i.parity_mode ),
        .updated_stop_bits_o     ( updated_config_i.stop_bits   ),
        .tx_idle                 ( tx_idle                      ),
        .rx_idle                 ( rx_idle                      ),
        .divisor_o               ( divisor                      ),
        .reset_bd_gen_o          ( reset_bd_gen                 ),
        .tx_fifo_full_i          ( tx_fifo_full                 ),
        .rx_fifo_empty_i         ( rx_fifo_empty                ),
        .rx_fifo_threshold_o     ( threshold                    ),
        .config_done_i           ( config_done                  ),
        .int_pend_i              ( !int_pending                 ),
        .communication_mode_o    ( communication_mode_i         ),
        .enable_config_o         ( enable_config_receive        ),
        .ack_request_o           ( req_ackn                     ),
        .set_std_config_o        ( set_std_config               ),
        .send_config_req_o       ( config_req_mst_i             ),
        .interrupt_id_i          ( interrupt_id                 ),
        .interrupt_id_en_i       ( enable_int_id                ),
        .rx_rdy_en_o             ( rx_rdy_en                    ),
        .frame_error_en_o        ( frame_error_en               ),
        .parity_error_en_o       ( parity_error_en              ),
        .overrun_error_en_o      ( overrun_error_en             ),
        .int_ackn_o              ( int_ackn                     ),
        .rx_data_i               ( data_rx                      ),
        .rx_fifo_read_o          ( rx_fifo_read_i               ),
        .tx_data_o               ( data_tx_i                    ),
        .tx_fifo_write_o         ( tx_fifo_write_i              )
    );

endmodule : uart