module control_unit (
	rst_n_i,
	clk_i,
	data_rx_i,
	data_tx_i,
	tx_done_i,
	req_done_i,
	rx_fifo_empty_i,
	rx_fifo_read_i,
	tx_fifo_full_i,
	tx_fifo_write_i,
	request_ack_i,
	enable_config_receive_i,
	config_req_slv_i,
	config_req_mst_i,
	config_i,
	updated_config_i,
	STR_en_o,
	config_o,
	config_req_mst_o,
	set_std_config_o,
	config_done_o,
	disable_global_int_o,
	rx_fifo_read_o,
	tx_fifo_write_o,
	data_tx_o,
	config_error_o
);
	input wire rst_n_i;
	input wire clk_i;
	input wire [7:0] data_rx_i;
	input wire [7:0] data_tx_i;
	input wire tx_done_i;
	input wire req_done_i;
	input wire rx_fifo_empty_i;
	input wire rx_fifo_read_i;
	input wire tx_fifo_full_i;
	input wire tx_fifo_write_i;
	input wire request_ack_i;
	input wire enable_config_receive_i;
	input wire config_req_slv_i;
	input wire config_req_mst_i;
	input wire [5:0] config_i;
	input wire [5:0] updated_config_i;
	output reg STR_en_o;
	output reg [5:0] config_o;
	output reg config_req_mst_o;
	output reg set_std_config_o;
	output reg config_done_o;
	output reg disable_global_int_o;
	output reg rx_fifo_read_o;
	output reg tx_fifo_write_o;
	output reg [7:0] data_tx_o;
	output reg config_error_o;
	localparam uart_pkg_SYSTEM_CLOCK_FREQ = 50000000;
	localparam uart_pkg_COUNT_10MS = 500000;
	reg [18:0] counter_10ms_CRT;
	reg [18:0] counter_10ms_NXT;
	always @(posedge clk_i or negedge rst_n_i) begin : ms50_counter
		if (!rst_n_i)
			counter_10ms_CRT <= 'b0;
		else if (counter_10ms_CRT == uart_pkg_COUNT_10MS)
			counter_10ms_CRT <= 'b0;
		else
			counter_10ms_CRT <= counter_10ms_NXT;
	end
	reg [1:0] config_failed_CRT;
	reg [1:0] config_failed_NXT;
	reg [1:0] config_packet_type_CRT;
	reg [1:0] config_packet_type_NXT;
	localparam DW_TYPE = 2'b00;
	localparam PM_TYPE = 2'b01;
	localparam SB_TYPE = 2'b10;
	localparam EC_TYPE = 2'b11;
	localparam uart_pkg_SYN_NUMBER = 3;
	reg [1:0] syn_data_cnt_CRT;
	reg [1:0] syn_data_cnt_NXT;
	always @(posedge clk_i or negedge rst_n_i) begin : datapath_register
		if (!rst_n_i) begin
			config_failed_CRT <= 'b0;
			config_packet_type_CRT <= 'b0;
			syn_data_cnt_CRT <= 2'b00;
		end
		else begin
			config_failed_CRT <= config_failed_NXT;
			config_packet_type_CRT <= config_packet_type_NXT;
			syn_data_cnt_CRT <= syn_data_cnt_NXT;
		end
	end
	reg [5:0] configuration_slv_CRT;
	reg [5:0] configuration_slv_NXT;
	reg data_width_load;
	reg parity_mode_load;
	reg stop_bits_number_load;
	always @(posedge clk_i or negedge rst_n_i)
		if (!rst_n_i)
			configuration_slv_CRT[5-:2] <= 2'b00;
		else if (data_width_load)
			configuration_slv_CRT[5-:2] <= configuration_slv_NXT[5-:2];
	always @(posedge clk_i or negedge rst_n_i)
		if (!rst_n_i)
			configuration_slv_CRT[3-:2] <= 2'b00;
		else if (parity_mode_load)
			configuration_slv_CRT[3-:2] <= configuration_slv_NXT[3-:2];
	always @(posedge clk_i or negedge rst_n_i)
		if (!rst_n_i)
			configuration_slv_CRT[1-:2] <= 2'b00;
		else if (stop_bits_number_load)
			configuration_slv_CRT[1-:2] <= configuration_slv_NXT[1-:2];
	reg [3:0] state_CRT;
	reg [3:0] state_NXT;
	always @(posedge clk_i or negedge rst_n_i) begin : fsm_state_register
		if (!rst_n_i)
			state_CRT <= 4'd9;
		else
			state_CRT <= state_NXT;
	end
	wire config_req_slv;
	assign config_req_slv = config_req_slv_i & enable_config_receive_i;
	localparam uart_pkg_ACKN_PKT = 8'hff;
	localparam [1:0] uart_pkg_DATA_WIDTH_ID = 2'b01;
	localparam [1:0] uart_pkg_END_CONFIGURATION_ID = 2'b00;
	localparam [1:0] uart_pkg_PARITY_MODE_ID = 2'b10;
	localparam [1:0] uart_pkg_STOP_BITS_ID = 2'b11;
	localparam uart_pkg_SYN = 8'h16;
	function [7:0] uart_pkg_assemble_packet;
		input reg [1:0] id;
		input reg [1:0] option;
		uart_pkg_assemble_packet = {4'b0000, option, id};
	endfunction
	always @(*) begin : fsm_next_state_logic
		state_NXT = state_CRT;
		counter_10ms_NXT = 'b0;
		config_failed_NXT = config_failed_CRT;
		config_packet_type_NXT = config_packet_type_CRT;
		syn_data_cnt_NXT = syn_data_cnt_CRT;
		configuration_slv_NXT = configuration_slv_CRT;
		STR_en_o = 1'b0;
		config_o = config_i;
		config_req_mst_o = 1'b0;
		config_error_o = 1'b0;
		config_done_o = 1'b0;
		set_std_config_o = 1'b0;
		data_width_load = 1'b0;
		parity_mode_load = 1'b0;
		stop_bits_number_load = 1'b0;
		disable_global_int_o = 1'b1;
		rx_fifo_read_o = 1'b0;
		tx_fifo_write_o = 1'b0;
		data_tx_o = data_tx_i;
		case (state_CRT)
			4'd8: begin
				set_std_config_o = 1'b1;
				disable_global_int_o = 1'b0;
				state_NXT = 4'd9;
			end
			4'd9: begin
				config_packet_type_NXT = 2'b00;
				config_done_o = 1'b1;
				disable_global_int_o = 1'b0;
				rx_fifo_read_o = rx_fifo_read_i;
				tx_fifo_write_o = tx_fifo_write_i;
				if (config_req_slv & request_ack_i)
					state_NXT = 4'd1;
				else if (config_req_mst_i)
					state_NXT = 4'd0;
			end
			4'd0:
				if ((syn_data_cnt_CRT != uart_pkg_SYN_NUMBER) & !tx_fifo_full_i) begin
					tx_fifo_write_o = 1'b1;
					data_tx_o = uart_pkg_SYN;
					syn_data_cnt_NXT = syn_data_cnt_CRT + 1'b1;
				end
				else begin
					config_req_mst_o = 1'b1;
					state_NXT = (req_done_i ? 4'd6 : 4'd0);
				end
			4'd6: begin
				counter_10ms_NXT = counter_10ms_CRT + 1'b1;
				config_req_mst_o = 1'b0;
				syn_data_cnt_NXT = 'b0;
				if (config_failed_CRT == 2'd3) begin
					config_error_o = 1'b1;
					config_failed_NXT = 2'b00;
					state_NXT = 4'd8;
				end
				else if (counter_10ms_CRT != uart_pkg_COUNT_10MS) begin
					rx_fifo_read_o = !rx_fifo_empty_i;
					if (data_rx_i == uart_pkg_ACKN_PKT)
						state_NXT = 4'd3;
				end
				else if (counter_10ms_CRT == uart_pkg_COUNT_10MS) begin
					config_failed_NXT = config_failed_CRT + 1'b1;
					state_NXT = 4'd0;
				end
			end
			4'd3: begin
				state_NXT = 4'd4;
				tx_fifo_write_o = 1'b1;
				case (config_packet_type_CRT)
					DW_TYPE: data_tx_o = uart_pkg_assemble_packet(uart_pkg_DATA_WIDTH_ID, updated_config_i[5-:2]);
					PM_TYPE: data_tx_o = uart_pkg_assemble_packet(uart_pkg_PARITY_MODE_ID, updated_config_i[3-:2]);
					SB_TYPE: data_tx_o = uart_pkg_assemble_packet(uart_pkg_STOP_BITS_ID, updated_config_i[1-:2]);
					EC_TYPE: data_tx_o = uart_pkg_assemble_packet(uart_pkg_END_CONFIGURATION_ID, 2'b00);
				endcase
			end
			4'd4:
				if (tx_done_i)
					state_NXT = 4'd7;
			4'd7: begin
				counter_10ms_NXT = counter_10ms_CRT + 1'b1;
				rx_fifo_read_o = !rx_fifo_empty_i;
				if (counter_10ms_CRT == uart_pkg_COUNT_10MS) begin
					state_NXT = 4'd8;
					config_error_o = 1'b1;
				end
				else if (data_rx_i == uart_pkg_ACKN_PKT) begin
					if (config_packet_type_CRT == EC_TYPE) begin
						state_NXT = 4'd9;
						config_done_o = 1'b1;
					end
					else
						state_NXT = 4'd3;
					config_packet_type_NXT = config_packet_type_CRT + 1'b1;
				end
			end
			4'd2: begin
				rx_fifo_read_o = !rx_fifo_empty_i;
				if (counter_10ms_CRT != uart_pkg_COUNT_10MS) begin
					if (!rx_fifo_empty_i) begin
						config_packet_type_NXT = config_packet_type_CRT + 1'b1;
						state_NXT = 4'd1;
					end
					case (data_rx_i[1-:2])
						uart_pkg_DATA_WIDTH_ID: begin
							configuration_slv_NXT[5-:2] = data_rx_i[3-:2];
							data_width_load = 1'b1;
						end
						uart_pkg_PARITY_MODE_ID: begin
							configuration_slv_NXT[3-:2] = data_rx_i[3-:2];
							parity_mode_load = 1'b1;
						end
						uart_pkg_STOP_BITS_ID: begin
							configuration_slv_NXT[1-:2] = data_rx_i[3-:2];
							stop_bits_number_load = 1'b1;
						end
					endcase
				end
				else begin
					state_NXT = 4'd8;
					config_error_o = 1'b1;
				end
			end
			4'd1: begin
				tx_fifo_write_o = 1'b1;
				data_tx_o = uart_pkg_ACKN_PKT;
				state_NXT = 4'd5;
			end
			4'd5:
				if (tx_done_i)
					if (config_packet_type_CRT == EC_TYPE) begin
						state_NXT = 4'd9;
						STR_en_o = 1'b1;
						config_o = configuration_slv_CRT;
					end
					else
						state_NXT = 4'd2;
		endcase
	end
endmodule
