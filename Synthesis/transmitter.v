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
module transmitter (
	clk_i,
	rst_n_i,
	enable,
	ov_baud_rt_i,
	data_tx_i,
	tx_fifo_write_i,
	config_req_mst_i,
	config_req_slv_i,
	request_ack_i,
	tx_data_stream_mode_i,
	data_width_i,
	stop_bits_number_i,
	parity_mode_i,
	tx_o,
	tx_done_o,
	req_done_o,
	tx_fifo_full_o,
	tx_idle_o
);
	input wire clk_i;
	input wire rst_n_i;
	input wire enable;
	input wire ov_baud_rt_i;
	input wire [7:0] data_tx_i;
	input wire tx_fifo_write_i;
	input wire config_req_mst_i;
	input wire config_req_slv_i;
	input wire request_ack_i;
	input wire tx_data_stream_mode_i;
	input wire [1:0] data_width_i;
	input wire [1:0] stop_bits_number_i;
	input wire [1:0] parity_mode_i;
	output reg tx_o;
	output reg tx_done_o;
	output reg req_done_o;
	output wire tx_fifo_full_o;
	output reg tx_idle_o;
	reg read_i;
	wire fifo_rst_n_i;
	wire fifo_full;
	wire fifo_empty;
	wire [7:0] fifo_data_read;
	localparam uart_pkg_TX_FIFO_DEPTH = 64;
	sync_FIFO_buffer #(
		.DATA_WIDTH(8),
		.FIFO_DEPTH(uart_pkg_TX_FIFO_DEPTH),
		.FWFT(1)
	) tx_fifo(
		.clk_i(clk_i),
		.rst_n_i(fifo_rst_n_i),
		.read_i(read_i),
		.write_i(tx_fifo_write_i),
		.wr_data_i(data_tx_i),
		.rd_data_o(fifo_data_read),
		.full_o(fifo_full),
		.empty_o(fifo_empty)
	);
	assign fifo_rst_n_i = rst_n_i | (config_req_slv_i & request_ack_i);
	assign tx_fifo_full_o = fifo_full;
	reg [7:0] data_tx_CRT;
	reg [7:0] data_tx_NXT;
	localparam uart_pkg_SYSTEM_CLOCK_FREQ = 50000000;
	localparam uart_pkg_COUNT_1MS = 50000;
	reg [15:0] counter_1ms_CRT;
	reg [15:0] counter_1ms_NXT;
	reg tx_line;
	reg [3:0] counter_br_CRT;
	reg [3:0] counter_br_NXT;
	reg stop_bits_CRT;
	reg stop_bits_NXT;
	reg [2:0] bits_processed_CRT;
	reg [2:0] bits_processed_NXT;
	localparam uart_pkg_TX_LINE_IDLE = 1;
	always @(posedge clk_i or negedge rst_n_i) begin : data_register
		if (!rst_n_i) begin
			data_tx_CRT <= 8'b00000000;
			counter_1ms_CRT <= 'b0;
			counter_br_CRT <= 4'b0000;
			bits_processed_CRT <= 3'b000;
			stop_bits_CRT <= 1'b0;
			tx_o <= uart_pkg_TX_LINE_IDLE;
		end
		else begin
			data_tx_CRT <= data_tx_NXT;
			counter_1ms_CRT <= counter_1ms_NXT;
			counter_br_CRT <= counter_br_NXT;
			bits_processed_CRT <= bits_processed_NXT;
			stop_bits_CRT <= stop_bits_NXT;
			tx_o <= tx_line;
		end
	end
	reg [2:0] state_CRT;
	reg [2:0] state_NXT;
	always @(posedge clk_i or negedge rst_n_i) begin : fsm_state_register
		if (!rst_n_i)
			state_CRT <= 3'd0;
		else if (config_req_slv_i)
			state_CRT <= 3'd0;
		else
			state_CRT <= state_NXT;
	end
	localparam [1:0] uart_pkg_DW_5BIT = 2'b00;
	localparam [1:0] uart_pkg_DW_6BIT = 2'b01;
	localparam [1:0] uart_pkg_DW_7BIT = 2'b10;
	localparam [1:0] uart_pkg_DW_8BIT = 2'b11;
	localparam [1:0] uart_pkg_SB_1BIT = 2'b00;
	localparam [1:0] uart_pkg_SB_2BIT = 2'b01;
	always @(*) begin : fsm_next_state_logic
		state_NXT = state_CRT;
		data_tx_NXT = data_tx_CRT;
		stop_bits_NXT = stop_bits_CRT;
		counter_br_NXT = counter_br_CRT;
		counter_1ms_NXT = counter_1ms_CRT;
		bits_processed_NXT = bits_processed_CRT;
		tx_line = uart_pkg_TX_LINE_IDLE;
		tx_done_o = 1'b0;
		tx_idle_o = 1'b0;
		read_i = 1'b0;
		req_done_o = 1'b0;
		case (state_CRT)
			3'd0: begin
				stop_bits_NXT = 1'b0;
				tx_idle_o = 1'b1;
				if (!fifo_empty & enable)
					state_NXT = 3'd2;
				else if (config_req_mst_i & fifo_empty)
					state_NXT = 3'd1;
			end
			3'd1: begin
				counter_1ms_NXT = counter_1ms_CRT + 1'b1;
				tx_line = !uart_pkg_TX_LINE_IDLE;
				if (counter_1ms_CRT == uart_pkg_COUNT_1MS) begin
					req_done_o = 1'b1;
					state_NXT = 3'd0;
					counter_1ms_NXT = 'b0;
				end
			end
			3'd2: begin
				tx_line = !uart_pkg_TX_LINE_IDLE;
				if (ov_baud_rt_i)
					if (counter_br_CRT == 4'd15) begin
						state_NXT = 3'd3;
						counter_br_NXT = 4'b0000;
						read_i = 1'b1;
						data_tx_NXT = fifo_data_read;
					end
					else
						counter_br_NXT = counter_br_CRT + 1'b1;
			end
			3'd3: begin
				tx_line = data_tx_CRT[0];
				if (ov_baud_rt_i)
					if (counter_br_CRT == 4'd15) begin
						data_tx_NXT = data_tx_CRT >> 1'b1;
						bits_processed_NXT = bits_processed_CRT + 1'b1;
						counter_br_NXT = 4'b0000;
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
						counter_br_NXT = counter_br_CRT + 1'b1;
			end
			3'd4: begin
				case (parity_mode_i[0])
					0: tx_line = ^data_tx_CRT ^ 1'b0;
					1: tx_line = ^data_tx_CRT ^ 1'b1;
				endcase
				if (ov_baud_rt_i)
					if (counter_br_CRT == 4'd15) begin
						counter_br_NXT = 4'b0000;
						state_NXT = 3'd5;
					end
					else
						counter_br_NXT = counter_br_CRT + 1'b1;
			end
			3'd5: begin
				tx_line = uart_pkg_TX_LINE_IDLE;
				bits_processed_NXT = 3'b000;
				if (ov_baud_rt_i)
					if (counter_br_CRT == 4'd15) begin
						case (stop_bits_number_i)
							uart_pkg_SB_1BIT: begin
								state_NXT = 3'd0;
								tx_done_o = (tx_data_stream_mode_i ? fifo_empty : 1'b1);
							end
							uart_pkg_SB_2BIT: begin
								state_NXT = (stop_bits_CRT ? 3'd0 : 3'd5);
								tx_done_o = (tx_data_stream_mode_i ? fifo_empty & stop_bits_CRT : stop_bits_CRT);
								stop_bits_NXT = 1'b1;
							end
							default: begin
								state_NXT = 3'd0;
								tx_done_o = (tx_data_stream_mode_i ? fifo_empty : 1'b1);
							end
						endcase
						counter_br_NXT = 4'b0000;
					end
					else
						counter_br_NXT = counter_br_CRT + 1'b1;
			end
		endcase
	end
endmodule
