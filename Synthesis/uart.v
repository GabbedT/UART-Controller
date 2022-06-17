module uart (
	clk_i,
	rst_n_i,
	chip_sel_n_i,
	address_i,
	read_write_i,
	rx_i,
	iack_i,
	data_io,
	tx_o,
	ireq_n_o
);
	input wire clk_i;
	input wire rst_n_i;
	input wire chip_sel_n_i;
	input wire [2:0] address_i;
	input wire read_write_i;
	input wire rx_i;
	input wire iack_i;
	inout wire [7:0] data_io;
	output wire tx_o;
	output wire ireq_n_o;
	reg rst_ff;
	reg rst_sync;
	always @(posedge clk_i or negedge rst_n_i) begin : reset_syncronizer
		if (!rst_n_i)
			{rst_sync, rst_ff} <= 2'b00;
		else
			{rst_sync, rst_ff} <= {rst_ff, 1'b1};
	end
	wire read_cs;
	wire write_cs;
	assign read_cs = read_write_i & !chip_sel_n_i;
	assign write_cs = !(read_write_i | chip_sel_n_i);
	wire read;
	wire write;
	edge_detector #(1) posedge_read_det(
		.clk_i(clk_i),
		.signal_i(read_cs),
		.edge_pulse_o(read)
	);
	edge_detector #(1) posedge_write_det(
		.clk_i(clk_i),
		.signal_i(write_cs),
		.edge_pulse_o(write)
	);
	wire int_ack;
	edge_detector #(1) posedge_ackn_det(
		.clk_i(clk_i),
		.signal_i(iack_i),
		.edge_pulse_o(int_ack)
	);
	wire [15:0] divisor;
	wire baud_rate_tick;
	wire reset_bd_n;
	wire reset_bd_gen;
	assign reset_bd_n = !reset_bd_gen & rst_sync;
	baud_rate_generator baud_rate_gen(
		.clk_i(clk_i),
		.rst_n_i(reset_bd_n),
		.divisor_i(divisor),
		.ov_baud_rt_o(baud_rate_tick)
	);
	wire [7:0] data_rx;
	wire [7:0] data_TXR;
	wire tx_done;
	wire req_done;
	wire rx_fifo_empty;
	wire rx_fifo_read;
	wire tx_fifo_write;
	wire tx_fifo_full;
	wire enable_configuration;
	wire configuration_received;
	wire send_configuration;
	wire [5:0] current_configuration;
	wire [5:0] next_configuration;
	wire [5:0] configuration_out;
	wire disable_global_interrupt;
	wire enable_STR;
	wire start_configuration;
	wire set_std_configuration;
	wire configuration_done;
	wire rx_read;
	wire tx_write;
	wire [7:0] data_tx;
	wire configuration_error;
	wire parity_error;
	wire acknowledge_request;
	control_unit controller(
		.clk_i(clk_i),
		.rst_n_i(rst_sync),
		.data_rx_i(data_rx),
		.data_tx_i(data_TXR),
		.tx_done_i(tx_done),
		.req_done_i(req_done),
		.rx_fifo_empty_i(rx_fifo_empty),
		.rx_fifo_read_i(rx_read),
		.tx_fifo_write_i(tx_write),
		.tx_fifo_full_i(tx_fifo_full),
		.request_ack_i(acknowledge_request),
		.enable_config_receive_i(enable_configuration),
		.config_req_slv_i(configuration_received),
		.config_req_mst_i(send_configuration),
		.config_i(current_configuration),
		.updated_config_i(next_configuration),
		.disable_global_int_o(disable_global_interrupt),
		.STR_en_o(enable_STR),
		.config_o(configuration_out),
		.config_req_mst_o(start_configuration),
		.set_std_config_o(set_std_configuration),
		.config_done_o(configuration_done),
		.rx_fifo_read_o(rx_fifo_read),
		.tx_fifo_write_o(tx_fifo_write),
		.data_tx_o(data_tx),
		.config_error_o(configuration_error)
	);
	wire tx_enable;
	wire tx_data_stream_mode;
	wire tx_idle;
	transmitter tx(
		.clk_i(clk_i),
		.rst_n_i(rst_sync),
		.enable(tx_enable),
		.ov_baud_rt_i(baud_rate_tick),
		.data_tx_i(data_tx),
		.tx_fifo_write_i(tx_fifo_write),
		.config_req_mst_i(start_configuration),
		.config_req_slv_i(configuration_received),
		.request_ack_i(acknowledge_request),
		.tx_data_stream_mode_i(tx_data_stream_mode),
		.data_width_i(current_configuration[5-:2]),
		.stop_bits_number_i(current_configuration[1-:2]),
		.parity_mode_i(current_configuration[3-:2]),
		.tx_o(tx_o),
		.tx_done_o(tx_done),
		.req_done_o(req_done),
		.tx_fifo_full_o(tx_fifo_full),
		.tx_idle_o(tx_idle)
	);
	wire rx_enable;
	wire [5:0] threshold;
	wire rx_data_stream_mode;
	wire rx_fifo_full;
	wire overrun_error;
	wire frame_error;
	wire data_rx_ready;
	wire rx_idle;
	receiver rx(
		.clk_i(clk_i),
		.rst_n_i(rst_sync),
		.enable(rx_enable),
		.ov_baud_rt_i(baud_rate_tick),
		.rx_i(rx_i),
		.rx_fifo_read_i(rx_fifo_read),
		.request_ack_i(acknowledge_request),
		.threshold_i(threshold),
		.rx_data_stream_mode_i(rx_data_stream_mode),
		.data_width_i(current_configuration[5-:2]),
		.stop_bits_number_i(current_configuration[1-:2]),
		.parity_mode_i(current_configuration[3-:2]),
		.rx_fifo_full_o(rx_fifo_full),
		.rx_fifo_empty_o(rx_fifo_empty),
		.config_req_slv_o(configuration_received),
		.overrun_error_o(overrun_error),
		.frame_error_o(frame_error),
		.parity_error_o(parity_error),
		.rx_data_ready_o(data_rx_ready),
		.data_rx_o(data_rx),
		.rx_idle_o(rx_idle)
	);
	wire [2:0] interrupt_vector;
	wire tx_done_interrupt_enable;
	wire store_interrupt_vector;
	wire overrun_error_interrupt_enable;
	wire frame_error_interrupt_enable;
	wire parity_error_interrupt_enable;
	wire data_rx_ready_interrupt_enable;
	wire interrupt_request;
	interrupt_arbiter arbiter(
		.clk_i(clk_i),
		.rst_n_i(rst_sync),
		.rx_dsm_i(rx_data_stream_mode),
		.rx_rdy_i(data_rx_ready),
		.tx_done_i(tx_done),
		.disable_interrupts_i(disable_global_interrupt),
		.config_error_i(configuration_error),
		.parity_error_i(parity_error),
		.frame_error_i(frame_error),
		.overrun_error_i(overrun_error),
		.rx_fifo_full_i(rx_fifo_full),
		.config_req_slv_i(configuration_received),
		.tx_done_en_i(tx_done_interrupt_enable),
		.overrun_error_en_i(overrun_error_interrupt_enable),
		.frame_error_en_i(frame_error_interrupt_enable),
		.parity_error_en_i(parity_error_interrupt_enable),
		.rx_rdy_en_i(data_rx_ready_interrupt_enable),
		.request_ack_i(acknowledge_request),
		.int_ackn_i(int_ack),
		.read_rx_data_i(rx_fifo_read),
		.rx_fifo_empty_i(rx_fifo_empty),
		.interrupt_vector_o(interrupt_vector),
		.store_int_vect_o(store_interrupt_vector),
		.ireq_n_o(interrupt_request)
	);
	assign ireq_n_o = interrupt_request;
	configuration_registers config_registers(
		.clk_i(clk_i),
		.rst_n_i(rst_sync),
		.read_i(read),
		.write_i(write),
		.address_i(address_i),
		.data_io(data_io),
		.tx_enable_o(tx_enable),
		.rx_enable_o(rx_enable),
		.int_ackn_i(int_ack),
		.tx_done_en_o(tx_done_interrupt_enable),
		.STR_en_i(enable_STR),
		.set_std_config_i(set_std_configuration),
		.data_width_i(configuration_out[5-:2]),
		.parity_mode_i(configuration_out[3-:2]),
		.stop_bits_i(configuration_out[1-:2]),
		.tx_dsm_o(tx_data_stream_mode),
		.rx_dsm_o(rx_data_stream_mode),
		.data_width_o(current_configuration[5-:2]),
		.parity_mode_o(current_configuration[3-:2]),
		.stop_bits_o(current_configuration[1-:2]),
		.updated_data_width_o(next_configuration[5-:2]),
		.updated_parity_mode_o(next_configuration[3-:2]),
		.updated_stop_bits_o(next_configuration[1-:2]),
		.tx_idle_i(tx_idle),
		.rx_idle_i(rx_idle),
		.divisor_o(divisor),
		.reset_bd_gen_o(reset_bd_gen),
		.tx_fifo_full_i(tx_fifo_full),
		.rx_fifo_empty_i(rx_fifo_empty),
		.rx_fifo_threshold_o(threshold),
		.configuration_done_i(configuration_done),
		.int_pending_i(interrupt_request),
		.enable_configuration_o(enable_configuration),
		.send_configuration_req_o(send_configuration),
		.acknowledge_request_o(acknowledge_request),
		.interrupt_vector_i(interrupt_vector),
		.interrupt_vector_en_i(store_interrupt_vector),
		.rx_rdy_en_o(data_rx_ready_interrupt_enable),
		.frame_error_en_o(frame_error_interrupt_enable),
		.parity_error_en_o(parity_error_interrupt_enable),
		.overrun_error_en_o(overrun_error_interrupt_enable),
		.rx_data_i(data_rx),
		.rx_fifo_read_o(rx_read),
		.tx_data_o(data_TXR),
		.tx_fifo_write_o(tx_write)
	);
endmodule
