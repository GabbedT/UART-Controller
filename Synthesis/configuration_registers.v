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
module configuration_registers (
	clk_i,
	rst_n_i,
	read_i,
	write_i,
	address_i,
	STR_en_i,
	set_std_config_i,
	data_io,
	data_width_i,
	parity_mode_i,
	stop_bits_i,
	tx_dsm_o,
	rx_dsm_o,
	data_width_o,
	parity_mode_o,
	stop_bits_o,
	updated_data_width_o,
	updated_parity_mode_o,
	updated_stop_bits_o,
	tx_idle_i,
	rx_idle_i,
	divisor_o,
	reset_bd_gen_o,
	tx_fifo_full_i,
	rx_fifo_empty_i,
	rx_fifo_threshold_o,
	configuration_done_i,
	int_pending_i,
	enable_configuration_o,
	send_configuration_req_o,
	acknowledge_request_o,
	tx_enable_o,
	rx_enable_o,
	int_ackn_i,
	interrupt_vector_i,
	interrupt_vector_en_i,
	tx_done_en_o,
	rx_rdy_en_o,
	frame_error_en_o,
	parity_error_en_o,
	overrun_error_en_o,
	rx_data_i,
	rx_fifo_read_o,
	tx_data_o,
	tx_fifo_write_o
);
	input wire clk_i;
	input wire rst_n_i;
	input wire read_i;
	input wire write_i;
	input wire [2:0] address_i;
	input wire STR_en_i;
	input wire set_std_config_i;
	inout wire [7:0] data_io;
	input wire [1:0] data_width_i;
	input wire [1:0] parity_mode_i;
	input wire [1:0] stop_bits_i;
	output wire tx_dsm_o;
	output wire rx_dsm_o;
	output wire [1:0] data_width_o;
	output wire [1:0] parity_mode_o;
	output wire [1:0] stop_bits_o;
	output wire [1:0] updated_data_width_o;
	output wire [1:0] updated_parity_mode_o;
	output wire [1:0] updated_stop_bits_o;
	input wire tx_idle_i;
	input wire rx_idle_i;
	output wire [15:0] divisor_o;
	output wire reset_bd_gen_o;
	input wire tx_fifo_full_i;
	input wire rx_fifo_empty_i;
	output wire [5:0] rx_fifo_threshold_o;
	input wire configuration_done_i;
	input wire int_pending_i;
	output wire enable_configuration_o;
	output wire send_configuration_req_o;
	output wire acknowledge_request_o;
	output wire tx_enable_o;
	output wire rx_enable_o;
	input wire int_ackn_i;
	input wire [2:0] interrupt_vector_i;
	input wire interrupt_vector_en_i;
	output wire tx_done_en_o;
	output wire rx_rdy_en_o;
	output wire frame_error_en_o;
	output wire parity_error_en_o;
	output wire overrun_error_en_o;
	input wire [7:0] rx_data_i;
	output wire rx_fifo_read_o;
	output wire [7:0] tx_data_o;
	output wire tx_fifo_write_o;
	reg [6:0] enable;
	wire enable_config_req;
	wire std_config;
	reg [7:0] STR_data;
	localparam [1:0] uart_pkg_DW_8BIT = 2'b11;
	localparam uart_pkg_STD_DATA_WIDTH = uart_pkg_DW_8BIT;
	localparam [1:0] uart_pkg_EVEN = 2'b00;
	localparam uart_pkg_STD_PARITY_MODE = uart_pkg_EVEN;
	localparam [1:0] uart_pkg_SB_1BIT = 2'b00;
	localparam uart_pkg_STD_STOP_BITS = uart_pkg_SB_1BIT;
	localparam uart_pkg_STD_CONFIGURATION = {uart_pkg_STD_STOP_BITS, uart_pkg_STD_PARITY_MODE, uart_pkg_STD_DATA_WIDTH};
	always @(posedge clk_i or negedge rst_n_i) begin : STR_WR
		if (!rst_n_i)
			STR_data <= {2'b00, uart_pkg_STD_CONFIGURATION};
		else if (set_std_config_i | std_config)
			STR_data <= {2'b00, uart_pkg_STD_CONFIGURATION};
		else if (STR_en_i & enable_config_req) begin
			STR_data[1-:2] <= data_width_i;
			STR_data[3-:2] <= parity_mode_i;
			STR_data[5-:2] <= stop_bits_i;
		end
		else if (enable[0])
			STR_data <= data_io;
	end
	assign updated_data_width_o = STR_data[1-:2];
	assign updated_parity_mode_o = STR_data[3-:2];
	assign updated_stop_bits_o = STR_data[5-:2];
	reg [1:0] data_width;
	reg [1:0] parity_mode;
	reg [1:0] stop_bits;
	wire config_done;
	edge_detector #(1) config_done_edge(
		.clk_i(clk_i),
		.signal_i(configuration_done_i),
		.edge_pulse_o(config_done)
	);
	always @(posedge clk_i or negedge rst_n_i) begin : config_register
		if (!rst_n_i) begin
			data_width <= uart_pkg_STD_DATA_WIDTH;
			parity_mode <= uart_pkg_STD_PARITY_MODE;
			stop_bits <= uart_pkg_STD_STOP_BITS;
		end
		else if (set_std_config_i | std_config) begin
			data_width <= uart_pkg_STD_DATA_WIDTH;
			parity_mode <= uart_pkg_STD_PARITY_MODE;
			stop_bits <= uart_pkg_STD_STOP_BITS;
		end
		else if (config_done) begin
			data_width <= STR_data[1-:2];
			parity_mode <= STR_data[3-:2];
			stop_bits <= STR_data[5-:2];
		end
		else if (STR_en_i & enable_config_req) begin
			data_width <= data_width_i;
			parity_mode <= parity_mode_i;
			stop_bits <= stop_bits_i;
		end
	end
	assign tx_dsm_o = STR_data[7];
	assign rx_dsm_o = STR_data[6];
	assign data_width_o = data_width;
	assign parity_mode_o = parity_mode;
	assign stop_bits_o = stop_bits;
	wire change_config;
	assign change_config = ((STR_data[1-:2] != data_width) | (STR_data[3-:2] != parity_mode)) | (STR_data[5-:2] != stop_bits);
	edge_detector #(1) config_change_edge(
		.clk_i(clk_i),
		.signal_i(change_config),
		.edge_pulse_o(send_configuration_req_o)
	);
	localparam LOWER = 0;
	localparam UPPER = 1;
	reg [15:0] DVR_data;
	localparam uart_pkg_STD_BAUD_RATE = 9600;
	localparam uart_pkg_SYSTEM_CLOCK_FREQ = 50000000;
	localparam uart_pkg_STD_DIVISOR = 32'sd324;
	always @(posedge clk_i or negedge rst_n_i) begin : DVR_WR
		if (!rst_n_i)
			DVR_data <= uart_pkg_STD_DIVISOR;
		else if (set_std_config_i | std_config)
			DVR_data <= uart_pkg_STD_DIVISOR;
		else if (enable[1])
			DVR_data[0+:8] <= data_io;
		else if (enable[2])
			DVR_data[8+:8] <= data_io;
	end
	reg [15:0] divisor_bdgen;
	wire DVR_done;
	reg [5:0] old_address;
	always @(posedge clk_i or negedge rst_n_i)
		if (!rst_n_i)
			old_address <= 6'b000000;
		else
			old_address <= {old_address[0+:3], address_i};
	localparam uart_pkg_LDVR_ADDR = 1;
	localparam uart_pkg_UDVR_ADDR = 2;
	assign DVR_done = (old_address[3+:3] == uart_pkg_LDVR_ADDR) & (old_address[0+:3] == uart_pkg_UDVR_ADDR);
	assign reset_bd_gen_o = DVR_done & (tx_idle_i & rx_idle_i);
	always @(posedge clk_i or negedge rst_n_i)
		if (!rst_n_i)
			divisor_bdgen <= uart_pkg_STD_DIVISOR;
		else if (set_std_config_i | std_config)
			divisor_bdgen <= uart_pkg_STD_DIVISOR;
		else if (DVR_done)
			divisor_bdgen <= DVR_data;
	assign divisor_o = (tx_idle_i & rx_idle_i ? divisor_bdgen : DVR_data);
	reg [7:0] FSR_data;
	always @(posedge clk_i or negedge rst_n_i) begin : FSR_WR
		if (!rst_n_i)
			FSR_data[5-:6] <= 6'b000000;
		else if (std_config)
			FSR_data[5-:6] <= 6'b000000;
		else if (enable[3])
			FSR_data[5-:6] <= data_io[5:0];
	end
	always @(posedge clk_i or negedge rst_n_i) begin : FSR_R
		if (!rst_n_i) begin
			FSR_data[7] <= 1'b0;
			FSR_data[6] <= 1'b1;
		end
		else begin
			FSR_data[7] <= tx_fifo_full_i;
			FSR_data[6] <= rx_fifo_empty_i;
		end
	end
	assign rx_fifo_threshold_o = FSR_data[5-:6];
	reg [7:0] CTR_data;
	localparam uart_pkg_FULL_DUPLEX = 2'b11;
	localparam uart_pkg_STD_COMM_MODE = uart_pkg_FULL_DUPLEX;
	always @(posedge clk_i or negedge rst_n_i) begin : CTR_WR
		if (!rst_n_i) begin
			CTR_data[7] <= 1'b0;
			CTR_data[5-:2] <= uart_pkg_STD_COMM_MODE;
			CTR_data[3] <= 1'b1;
		end
		else if (set_std_config_i | std_config) begin
			CTR_data[7] <= 1'b0;
			CTR_data[5-:2] <= uart_pkg_STD_COMM_MODE;
			CTR_data[3] <= 1'b1;
		end
		else if (enable[4]) begin
			CTR_data[7] <= data_io[6];
			CTR_data[5-:2] <= data_io[4:3];
			CTR_data[3] <= data_io[2];
		end
	end
	assign std_config = CTR_data[1];
	always @(posedge clk_i or negedge rst_n_i) begin : CTR_R
		if (!rst_n_i) begin
			CTR_data[2] <= 1'b1;
			CTR_data[6] <= 1'b0;
		end
		else begin
			CTR_data[2] <= configuration_done_i;
			CTR_data[6] <= !int_pending_i;
		end
	end
	assign enable_config_req = CTR_data[3];
	always @(posedge clk_i or negedge rst_n_i)
		if (!rst_n_i) begin
			CTR_data[1] <= 1'b0;
			CTR_data[0] <= 1'b0;
		end
		else if (enable[4]) begin
			CTR_data[1] <= data_io[1];
			CTR_data[0] <= data_io[0];
		end
		else begin
			CTR_data[1] <= 1'b0;
			CTR_data[0] <= 1'b0;
		end
	assign tx_enable_o = CTR_data[4];
	assign rx_enable_o = CTR_data[5];
	assign enable_configuration_o = enable_config_req;
	assign acknowledge_request_o = CTR_data[0];
	reg [7:0] ISR_data;
	always @(posedge clk_i or negedge rst_n_i) begin : ISR_WR
		if (!rst_n_i) begin
			ISR_data[7] <= 1'b1;
			ISR_data[6] <= 1'b1;
			ISR_data[5] <= 1'b1;
			ISR_data[4] <= 1'b1;
			ISR_data[3] <= 1'b1;
		end
		else if (std_config) begin
			ISR_data[7] <= 1'b1;
			ISR_data[6] <= 1'b1;
			ISR_data[5] <= 1'b1;
			ISR_data[4] <= 1'b1;
			ISR_data[3] <= 1'b1;
		end
		else if (enable[5]) begin
			ISR_data[7] <= data_io[6];
			ISR_data[6] <= data_io[6];
			ISR_data[5] <= data_io[5];
			ISR_data[4] <= data_io[4];
			ISR_data[3] <= data_io[3];
		end
	end
	always @(posedge clk_i or negedge rst_n_i) begin : ISR_R
		if (!rst_n_i)
			ISR_data[2-:3] <= 3'b000;
		else if (interrupt_vector_en_i)
			ISR_data[2-:3] <= interrupt_vector_i;
	end
	assign overrun_error_en_o = ISR_data[3];
	assign parity_error_en_o = ISR_data[4];
	assign frame_error_en_o = ISR_data[5];
	assign tx_done_en_o = ISR_data[7];
	assign rx_rdy_en_o = ISR_data[6];
	wire rx_fifo_empty_edge;
	edge_detector #(0) empty_fifo_negedge(
		.clk_i(clk_i),
		.signal_i(rx_fifo_empty_i),
		.edge_pulse_o(rx_fifo_empty_edge)
	);
	reg [7:0] RXR_data;
	wire rx_fifo_read;
	always @(posedge clk_i or negedge rst_n_i) begin : RXR_WR
		if (!rst_n_i)
			RXR_data <= 8'b00000000;
		else if (rx_fifo_read)
			RXR_data <= rx_data_i;
	end
	localparam uart_pkg_RXR_ADDR = 6;
	assign rx_fifo_read = ((!rx_fifo_empty_i & read_i) & (address_i == uart_pkg_RXR_ADDR)) | rx_fifo_empty_edge;
	assign rx_fifo_read_o = rx_fifo_read;
	reg [7:0] TXR_data;
	always @(posedge clk_i or negedge rst_n_i)
		if (!rst_n_i)
			TXR_data <= 8'b00000000;
		else if (enable[6])
			TXR_data <= data_io;
	reg write_ff;
	always @(posedge clk_i or negedge rst_n_i)
		if (!rst_n_i)
			write_ff <= 1'b0;
		else
			write_ff <= write_i;
	assign tx_data_o = TXR_data;
	localparam uart_pkg_TXR_ADDR = 7;
	assign tx_fifo_write_o = write_ff & (address_i == uart_pkg_TXR_ADDR);
	reg [7:0] data_register;
	localparam uart_pkg_CTR_ADDR = 4;
	localparam uart_pkg_FSR_ADDR = 3;
	localparam uart_pkg_ISR_ADDR = 5;
	localparam uart_pkg_STR_ADDR = 0;
	always @(*) begin : decoder
		enable = 8'b00000000;
		data_register = 8'b00000000;
		if (write_i)
			case (address_i)
				uart_pkg_STR_ADDR: enable[0] = 1'b1;
				uart_pkg_LDVR_ADDR: enable[1] = 1'b1;
				uart_pkg_UDVR_ADDR: enable[2] = 1'b1;
				uart_pkg_FSR_ADDR: enable[3] = 1'b1;
				uart_pkg_CTR_ADDR: enable[4] = 1'b1;
				uart_pkg_ISR_ADDR: enable[5] = 1'b1;
				uart_pkg_TXR_ADDR: enable[6] = 1'b1;
				default: enable = 8'b00000000;
			endcase
		else if (read_i)
			case (address_i)
				uart_pkg_STR_ADDR: data_register = STR_data;
				uart_pkg_LDVR_ADDR: data_register = DVR_data[0+:8];
				uart_pkg_UDVR_ADDR: data_register = DVR_data[8+:8];
				uart_pkg_FSR_ADDR: data_register = FSR_data;
				uart_pkg_CTR_ADDR: data_register = CTR_data;
				uart_pkg_ISR_ADDR: data_register = ISR_data;
				uart_pkg_RXR_ADDR: data_register = RXR_data;
				uart_pkg_TXR_ADDR: data_register = TXR_data;
				default: data_register = 8'b00000000;
			endcase
	end
	reg [7:0] data;
	localparam uart_pkg_UART_ISR_VECTOR = 8'hff;
	always @(*)
		if ((CTR_data[7] & !int_pending_i) & int_ackn_i)
			data = uart_pkg_UART_ISR_VECTOR;
		else
			data = data_register;
	assign data_io = (read_i ? data : 8'bzzzzzzzz);
endmodule
