module sync_FIFO_buffer (
	clk_i,
	rst_n_i,
	read_i,
	write_i,
	wr_data_i,
	rd_data_o,
	full_o,
	empty_o
);
	parameter DATA_WIDTH = 32;
	parameter FIFO_DEPTH = 32;
	parameter FWFT = 1;
	input wire clk_i;
	input wire rst_n_i;
	input wire read_i;
	input wire write_i;
	input wire [DATA_WIDTH - 1:0] wr_data_i;
	output reg [DATA_WIDTH - 1:0] rd_data_o;
	output reg full_o;
	output reg empty_o;
	localparam CRT = 0;
	localparam NXT = 1;
	localparam ADDR_BITS = $clog2(FIFO_DEPTH);
	localparam [1:0] READ = 2'b01;
	localparam [1:0] WRITE = 2'b10;
	localparam [1:0] BOTH = 2'b11;
	wire [ADDR_BITS - 1:0] wr_addr;
	wire [ADDR_BITS - 1:0] rd_addr;
	reg full;
	reg empty;
	wire write_en;
	wire read_en;
	reg [DATA_WIDTH - 1:0] FIFO_memory [FIFO_DEPTH - 1:0];
	generate
		if (FWFT == 1) begin : FWFT_configuration
			always @(posedge clk_i)
				if (write_en)
					FIFO_memory[wr_addr] <= wr_data_i;
			wire [DATA_WIDTH:1] sv2v_tmp_DD11B;
			assign sv2v_tmp_DD11B = FIFO_memory[rd_addr];
			always @(*) rd_data_o = sv2v_tmp_DD11B;
		end
		else begin : standard_configuration
			always @(posedge clk_i)
				if (write_en & read_en) begin
					FIFO_memory[wr_addr] <= wr_data_i;
					rd_data_o <= FIFO_memory[rd_addr];
				end
				else if (read_en)
					rd_data_o <= FIFO_memory[rd_addr];
				else if (write_en)
					FIFO_memory[wr_addr] <= wr_data_i;
		end
	endgenerate
	reg [ADDR_BITS - 1:0] write_ptr_CRT;
	reg [ADDR_BITS - 1:0] write_ptr_NXT;
	reg [ADDR_BITS - 1:0] read_ptr_CRT;
	reg [ADDR_BITS - 1:0] read_ptr_NXT;
	wire [ADDR_BITS - 1:0] write_ptr_inc;
	wire [ADDR_BITS - 1:0] read_ptr_inc;
	assign write_en = write_i & !full_o;
	assign read_en = read_i & !empty_o;
	assign wr_addr = write_ptr_CRT;
	assign rd_addr = read_ptr_CRT;
	always @(posedge clk_i or negedge rst_n_i) begin : status_register
		if (!rst_n_i) begin
			write_ptr_CRT <= 'b0;
			read_ptr_CRT <= 'b0;
			full_o <= 1'b0;
			empty_o <= 1'b1;
		end
		else begin
			write_ptr_CRT <= write_ptr_NXT;
			read_ptr_CRT <= read_ptr_NXT;
			full_o <= full;
			empty_o <= empty;
		end
	end
	generate
		if (FIFO_DEPTH == (2 ** $clog2(FIFO_DEPTH))) begin : genblk2
			assign write_ptr_inc = write_ptr_CRT + 1;
			assign read_ptr_inc = read_ptr_CRT + 1;
		end
		else begin : genblk2
			assign write_ptr_inc = (write_ptr_CRT == (FIFO_DEPTH - 1) ? 'b0 : write_ptr_CRT + 1'b1);
			assign read_ptr_inc = (read_ptr_CRT == (FIFO_DEPTH - 1) ? 'b0 : read_ptr_CRT + 1'b1);
		end
	endgenerate
	always @(*) begin : next_state_logic
		write_ptr_NXT = write_ptr_CRT;
		read_ptr_NXT = read_ptr_CRT;
		empty = empty_o;
		full = full_o;
		case ({write_i, read_i})
			READ:
				if (!empty_o) begin
					read_ptr_NXT = read_ptr_inc;
					full = 1'b0;
					empty = write_ptr_CRT == read_ptr_inc;
					write_ptr_NXT = write_ptr_CRT;
				end
			WRITE:
				if (!full_o) begin
					write_ptr_NXT = write_ptr_inc;
					empty = 1'b0;
					full = read_ptr_CRT == write_ptr_inc;
					read_ptr_NXT = read_ptr_CRT;
				end
			BOTH: begin
				write_ptr_NXT = write_ptr_inc;
				read_ptr_NXT = read_ptr_inc;
			end
		endcase
	end
endmodule
module receiver (
	clk_i,
	rst_n_i,
	enable,
	ov_baud_rt_i,
	rx_i,
	rx_fifo_read_i,
	request_ack_i,
	threshold_i,
	rx_data_stream_mode_i,
	data_width_i,
	stop_bits_number_i,
	parity_mode_i,
	rx_fifo_full_o,
	rx_fifo_empty_o,
	config_req_slv_o,
	overrun_error_o,
	frame_error_o,
	parity_error_o,
	rx_data_ready_o,
	data_rx_o,
	rx_idle_o
);
	input wire clk_i;
	input wire rst_n_i;
	input wire enable;
	input wire ov_baud_rt_i;
	input wire rx_i;
	input wire rx_fifo_read_i;
	input wire request_ack_i;
	input wire [5:0] threshold_i;
	input wire rx_data_stream_mode_i;
	input wire [1:0] data_width_i;
	input wire [1:0] stop_bits_number_i;
	input wire [1:0] parity_mode_i;
	output wire rx_fifo_full_o;
	output wire rx_fifo_empty_o;
	output wire config_req_slv_o;
	output wire overrun_error_o;
	output wire frame_error_o;
	output wire parity_error_o;
	output wire rx_data_ready_o;
	output wire [7:0] data_rx_o;
	output reg rx_idle_o;
	localparam FRAME = 8;
	localparam OVERRUN = 9;
	localparam PARITY = 10;
	wire read_i;
	wire fifo_rst_n_i;
	reg fifo_write;
	wire fifo_read;
	wire fifo_full;
	wire fifo_empty;
	wire [10:0] fifo_data_read;
	reg [10:0] fifo_data_write;
	localparam uart_pkg_RX_FIFO_DEPTH = 64;
	sync_FIFO_buffer #(
		.DATA_WIDTH(11),
		.FIFO_DEPTH(uart_pkg_RX_FIFO_DEPTH),
		.FWFT(1)
	) rx_fifo(
		.clk_i(clk_i),
		.rst_n_i(fifo_rst_n_i),
		.read_i(fifo_read),
		.write_i(fifo_write),
		.wr_data_i(fifo_data_write),
		.rd_data_o(fifo_data_read),
		.full_o(fifo_full),
		.empty_o(fifo_empty)
	);
	reg fifo_rst_n;
	assign fifo_rst_n_i = rst_n_i & fifo_rst_n;
	assign fifo_read = rx_fifo_read_i;
	assign rx_fifo_empty_o = fifo_empty;
	reg [7:0] data_rx_CRT;
	reg [7:0] data_rx_NXT;
	reg [3:0] counter_16br_CRT;
	reg [3:0] counter_16br_NXT;
	reg [2:0] bits_processed_CRT;
	reg [2:0] bits_processed_NXT;
	reg stop_bits_cnt_CRT;
	reg stop_bits_cnt_NXT;
	reg parity_bit_CRT;
	reg parity_bit_NXT;
	reg stop_bits_CRT;
	reg stop_bits_NXT;
	localparam uart_pkg_SYN_NUMBER = 3;
	reg [1:0] syn_data_cnt_CRT;
	reg [1:0] syn_data_cnt_NXT;
	always @(posedge clk_i or negedge rst_n_i)
		if (!rst_n_i) begin
			data_rx_CRT <= 8'b00000000;
			counter_16br_CRT <= 4'b0000;
			bits_processed_CRT <= 3'b000;
			stop_bits_cnt_CRT <= 1'b0;
			parity_bit_CRT <= 1'b0;
			stop_bits_CRT <= 1'b1;
			syn_data_cnt_CRT <= 2'b00;
		end
		else begin
			data_rx_CRT <= data_rx_NXT;
			counter_16br_CRT <= counter_16br_NXT;
			bits_processed_CRT <= bits_processed_NXT;
			stop_bits_cnt_CRT <= stop_bits_cnt_NXT;
			parity_bit_CRT <= parity_bit_NXT;
			stop_bits_CRT <= stop_bits_NXT;
			syn_data_cnt_CRT <= syn_data_cnt_NXT;
		end
	localparam uart_pkg_SYSTEM_CLOCK_FREQ = 50000000;
	localparam uart_pkg_COUNT_1MS = 50000;
	reg [15:0] counter_1ms_CRT;
	reg [15:0] counter_1ms_NXT;
	always @(posedge clk_i or negedge rst_n_i) begin : ms10_counter
		if (!rst_n_i)
			counter_1ms_CRT <= 'b0;
		else
			counter_1ms_CRT <= counter_1ms_NXT;
	end
	localparam uart_pkg_RX_LINE_IDLE = 1;
	always @(*) begin : ms10_counter_logic
		if (rx_i != uart_pkg_RX_LINE_IDLE)
			counter_1ms_NXT = counter_1ms_CRT + 1'b1;
		else if (counter_1ms_CRT == uart_pkg_COUNT_1MS)
			counter_1ms_NXT = 'b0;
		else
			counter_1ms_NXT = 'b0;
	end
	reg [5:0] fifo_size_cnt_CRT;
	reg [5:0] fifo_size_cnt_NXT;
	always @(posedge clk_i or negedge rst_n_i) begin : fifo_size_counter
		if (!rst_n_i)
			fifo_size_cnt_CRT <= 'b0;
		else
			fifo_size_cnt_CRT <= fifo_size_cnt_NXT;
	end
	always @(*) begin : fifo_size_counter_logic
		case ({fifo_write, fifo_read})
			2'b10: fifo_size_cnt_NXT = fifo_size_cnt_CRT + 1'b1;
			2'b01: fifo_size_cnt_NXT = fifo_size_cnt_CRT - 1'b1;
			default: fifo_size_cnt_NXT = fifo_size_cnt_CRT;
		endcase
	end
	reg cfg_req_CRT;
	reg cfg_req_NXT;
	always @(posedge clk_i or negedge rst_n_i)
		if (!rst_n_i)
			cfg_req_CRT <= 1'b0;
		else if (request_ack_i)
			cfg_req_CRT <= 1'b0;
		else
			cfg_req_CRT <= cfg_req_NXT;
	assign config_req_slv_o = cfg_req_CRT;
	reg [2:0] state_CRT;
	reg [2:0] state_NXT;
	always @(posedge clk_i or negedge rst_n_i) begin : fsm_state_register
		if (!rst_n_i)
			state_CRT <= 3'd0;
		else if (!fifo_rst_n)
			state_CRT <= 3'd0;
		else
			state_CRT <= state_NXT;
	end
	reg data_ready;
	localparam [1:0] uart_pkg_DW_5BIT = 2'b00;
	localparam [1:0] uart_pkg_DW_6BIT = 2'b01;
	localparam [1:0] uart_pkg_DW_7BIT = 2'b10;
	localparam [1:0] uart_pkg_DW_8BIT = 2'b11;
	localparam [1:0] uart_pkg_SB_2BIT = 2'b01;
	localparam uart_pkg_SYN = 8'h16;
	always @(*) begin
		state_NXT = state_CRT;
		data_rx_NXT = data_rx_CRT;
		stop_bits_NXT = stop_bits_CRT;
		parity_bit_NXT = parity_bit_CRT;
		counter_16br_NXT = counter_16br_CRT;
		syn_data_cnt_NXT = syn_data_cnt_CRT;
		stop_bits_cnt_NXT = stop_bits_cnt_CRT;
		bits_processed_NXT = bits_processed_CRT;
		cfg_req_NXT = cfg_req_CRT;
		rx_idle_o = 1'b0;
		fifo_write = 1'b0;
		fifo_rst_n = 1'b1;
		case (state_CRT)
			3'd0: begin
				stop_bits_cnt_NXT = 1'b0;
				stop_bits_NXT = 1'b0;
				rx_idle_o = 1'b1;
				if ((rx_i != uart_pkg_RX_LINE_IDLE) & enable) begin
					counter_16br_NXT = 4'b0000;
					state_NXT = (syn_data_cnt_CRT == uart_pkg_SYN_NUMBER ? 3'd1 : 3'd2);
				end
			end
			3'd1: begin
				syn_data_cnt_NXT = 'b0;
				if (rx_i == uart_pkg_RX_LINE_IDLE)
					state_NXT = 3'd0;
				else if (counter_1ms_CRT == uart_pkg_COUNT_1MS) begin
					cfg_req_NXT = 1'b1;
					state_NXT = 3'd0;
					fifo_rst_n = !request_ack_i;
				end
			end
			3'd2:
				if (ov_baud_rt_i)
					if (counter_16br_CRT == 4'd7) begin
						bits_processed_NXT = 3'b000;
						counter_16br_NXT = 4'b0000;
						state_NXT = 3'd3;
					end
					else
						counter_16br_NXT = counter_16br_CRT + 1'b1;
			3'd3: begin
				stop_bits_NXT = 1'b1;
				if (ov_baud_rt_i)
					if (counter_16br_CRT == 4'd15) begin
						counter_16br_NXT = 4'b0000;
						bits_processed_NXT = bits_processed_CRT + 1'b1;
						data_rx_NXT = {rx_i, data_rx_CRT[7:1]};
						if (parity_mode_i[1])
							case (data_width_i)
								uart_pkg_DW_5BIT: state_NXT = (bits_processed_CRT == 4'd4 ? 3'd5 : 3'd3);
								uart_pkg_DW_6BIT: state_NXT = (bits_processed_CRT == 4'd5 ? 3'd5 : 3'd3);
								uart_pkg_DW_7BIT: state_NXT = (bits_processed_CRT == 4'd6 ? 3'd5 : 3'd3);
								uart_pkg_DW_8BIT: state_NXT = (bits_processed_CRT == 4'd7 ? 3'd5 : 3'd3);
							endcase
						else
							case (data_width_i)
								uart_pkg_DW_5BIT: state_NXT = (bits_processed_CRT == 4'd4 ? 3'd4 : 3'd3);
								uart_pkg_DW_6BIT: state_NXT = (bits_processed_CRT == 4'd5 ? 3'd4 : 3'd3);
								uart_pkg_DW_7BIT: state_NXT = (bits_processed_CRT == 4'd6 ? 3'd4 : 3'd3);
								uart_pkg_DW_8BIT: state_NXT = (bits_processed_CRT == 4'd7 ? 3'd4 : 3'd3);
							endcase
					end
					else
						counter_16br_NXT = counter_16br_CRT + 1'b1;
			end
			3'd4:
				if (ov_baud_rt_i)
					if (counter_16br_CRT == 4'd15) begin
						counter_16br_NXT = 4'b0000;
						parity_bit_NXT = rx_i;
						state_NXT = 3'd5;
					end
					else
						counter_16br_NXT = counter_16br_CRT + 1'b1;
			3'd5: begin
				if (ov_baud_rt_i)
					if (counter_16br_CRT == 4'd15) begin
						stop_bits_NXT = stop_bits_CRT & rx_i;
						case (stop_bits_number_i)
							uart_pkg_SB_2BIT: begin
								stop_bits_cnt_NXT = 1'b1;
								state_NXT = (stop_bits_cnt_CRT ? 3'd0 : 3'd5);
								fifo_write = stop_bits_cnt_CRT & !fifo_full;
							end
							default: begin
								state_NXT = 3'd0;
								fifo_write = !fifo_full;
							end
						endcase
					end
					else
						counter_16br_NXT = counter_16br_CRT + 1'b1;
				if (state_NXT == 3'd0)
					if (data_rx_CRT == uart_pkg_SYN)
						syn_data_cnt_NXT = syn_data_cnt_CRT + 1'b1;
					else
						syn_data_cnt_NXT = 'b0;
			end
		endcase
	end
	always @(*) begin : rx_done_interrupt_logic
		if ((state_NXT == 3'd0) & (state_CRT == 3'd5)) begin
			if (rx_data_stream_mode_i) begin
				if (threshold_i != 'b0)
					data_ready = fifo_size_cnt_CRT >= threshold_i;
				else
					data_ready = fifo_full;
			end
			else
				data_ready = 1'b1;
		end
		else
			data_ready = 1'b0;
	end
	always @(*) begin : fifo_write_data_assignment
		case (data_width_i)
			uart_pkg_DW_5BIT: fifo_data_write[7:0] = {3'b000, data_rx_CRT[7:3]};
			uart_pkg_DW_6BIT: fifo_data_write[7:0] = {2'b00, data_rx_CRT[7:2]};
			uart_pkg_DW_7BIT: fifo_data_write[7:0] = {1'b0, data_rx_CRT[7:1]};
			uart_pkg_DW_8BIT: fifo_data_write[7:0] = data_rx_CRT[7:0];
		endcase
		fifo_data_write[FRAME] = (state_CRT == 3'd5) & !rx_i;
		fifo_data_write[OVERRUN] = fifo_full & (state_CRT != 3'd0);
	end
	assign data_rx_o = (rx_fifo_read_i ? fifo_data_read[7:0] : 8'b00000000);
	assign rx_data_ready_o = data_ready;
	assign rx_fifo_full_o = (rx_data_stream_mode_i & (threshold_i == 6'b000000) ? 1'b0 : fifo_full);
	reg parity;
	localparam [1:0] uart_pkg_EVEN = 2'b00;
	localparam [1:0] uart_pkg_ODD = 2'b01;
	always @(*) begin : parity_detection_logic
		case (data_width_i)
			uart_pkg_DW_5BIT: parity = ^data_rx_CRT[4:0];
			uart_pkg_DW_6BIT: parity = ^data_rx_CRT[5:0];
			uart_pkg_DW_7BIT: parity = ^data_rx_CRT[6:0];
			uart_pkg_DW_8BIT: parity = ^data_rx_CRT;
		endcase
		case (parity_mode_i)
			uart_pkg_EVEN: fifo_data_write[PARITY] = parity_bit_CRT != (parity ^ 1'b0);
			uart_pkg_ODD: fifo_data_write[PARITY] = parity_bit_CRT != (parity ^ 1'b1);
			default: fifo_data_write[PARITY] = 1'b0;
		endcase
	end
	assign frame_error_o = fifo_data_read[FRAME] & rx_fifo_read_i;
	assign overrun_error_o = fifo_data_read[OVERRUN] & rx_fifo_read_i;
	assign parity_error_o = fifo_data_read[PARITY] & rx_fifo_read_i;
endmodule
