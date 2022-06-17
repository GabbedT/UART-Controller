module interrupt_arbiter (
	clk_i,
	rst_n_i,
	rx_dsm_i,
	disable_interrupts_i,
	rx_rdy_i,
	tx_done_i,
	config_error_i,
	parity_error_i,
	frame_error_i,
	overrun_error_i,
	rx_fifo_full_i,
	config_req_slv_i,
	overrun_error_en_i,
	frame_error_en_i,
	parity_error_en_i,
	rx_rdy_en_i,
	tx_done_en_i,
	request_ack_i,
	int_ackn_i,
	read_rx_data_i,
	rx_fifo_empty_i,
	interrupt_vector_o,
	store_int_vect_o,
	ireq_n_o
);
	input wire clk_i;
	input wire rst_n_i;
	input wire rx_dsm_i;
	input wire disable_interrupts_i;
	input wire rx_rdy_i;
	input wire tx_done_i;
	input wire config_error_i;
	input wire parity_error_i;
	input wire frame_error_i;
	input wire overrun_error_i;
	input wire rx_fifo_full_i;
	input wire config_req_slv_i;
	input wire overrun_error_en_i;
	input wire frame_error_en_i;
	input wire parity_error_en_i;
	input wire rx_rdy_en_i;
	input wire tx_done_en_i;
	input wire request_ack_i;
	input wire int_ackn_i;
	input wire read_rx_data_i;
	input wire rx_fifo_empty_i;
	output wire [2:0] interrupt_vector_o;
	output reg store_int_vect_o;
	output reg ireq_n_o;
	wire overrun_error;
	wire parity_error;
	wire frame_error;
	wire rx_rdy;
	wire tx_done;
	assign tx_done = tx_done_i & tx_done_en_i;
	assign overrun_error = overrun_error_i & overrun_error_en_i;
	assign parity_error = (parity_error_i & parity_error_en_i) & rx_rdy_i;
	assign frame_error = frame_error_i & frame_error_en_i;
	assign rx_rdy = ((frame_error | parity_error) | overrun_error ? 1'b0 : rx_rdy_i & rx_rdy_en_i);
	localparam CFG_ERROR = 3;
	localparam OVR_ERROR = 2;
	localparam FRM_ERROR = 1;
	localparam PAR_ERROR = 0;
	wire p1_enable_load;
	reg [3:0] p1_reset;
	reg [3:0] p1_int_bundle_CRT;
	wire [3:0] p1_int_bundle_NXT;
	genvar i;
	generate
		for (i = 0; i < 4; i = i + 1) begin : genblk1
			always @(posedge clk_i or negedge rst_n_i)
				if (!rst_n_i)
					p1_int_bundle_CRT[i] <= 1'b0;
				else if (p1_reset[i] | disable_interrupts_i)
					p1_int_bundle_CRT[i] <= 1'b0;
				else if (p1_enable_load)
					p1_int_bundle_CRT[i] <= p1_int_bundle_NXT[i];
		end
	endgenerate
	assign p1_int_bundle_NXT = {config_error_i, overrun_error, frame_error, parity_error};
	assign p1_enable_load = |p1_int_bundle_NXT;
	reg [2:0] p1_int_vector;
	localparam uart_pkg_INT_CONFIG_FAIL = 3'b001;
	localparam uart_pkg_INT_FRAME = 3'b011;
	localparam uart_pkg_INT_OVERRUN = 3'b010;
	localparam uart_pkg_INT_PARITY = 3'b100;
	always @(*) begin : prio1_vector_gen
		casez (p1_int_bundle_NXT)
			4'b1zzz: p1_int_vector = uart_pkg_INT_CONFIG_FAIL;
			4'b01zz: p1_int_vector = uart_pkg_INT_OVERRUN;
			4'b001z: p1_int_vector = uart_pkg_INT_FRAME;
			4'b0001: p1_int_vector = uart_pkg_INT_PARITY;
			default: p1_int_vector = 3'b000;
		endcase
	end
	localparam RX_FULL = 1;
	localparam RX_RDY = 0;
	wire p2_enable_load;
	reg [1:0] p2_reset;
	reg [1:0] p2_int_bundle_CRT;
	wire [1:0] p2_int_bundle_NXT;
	genvar j;
	generate
		for (j = 0; j < 2; j = j + 1) begin : genblk2
			always @(posedge clk_i or negedge rst_n_i)
				if (!rst_n_i)
					p2_int_bundle_CRT[j] <= 1'b0;
				else if (p2_reset[j] | disable_interrupts_i)
					p2_int_bundle_CRT[j] <= 1'b0;
				else if (p2_enable_load)
					p2_int_bundle_CRT[j] <= p2_int_bundle_NXT[j];
		end
	endgenerate
	assign p2_int_bundle_NXT = {rx_fifo_full_i, rx_rdy};
	assign p2_enable_load = |p2_int_bundle_NXT;
	reg [2:0] p2_int_vector;
	localparam uart_pkg_INT_RXD_RDY = 3'b101;
	localparam uart_pkg_INT_RX_FULL = 3'b110;
	always @(*) begin : prio2_vector_gen
		casez (p2_int_bundle_NXT)
			2'b1z: p2_int_vector = uart_pkg_INT_RX_FULL;
			2'b01: p2_int_vector = uart_pkg_INT_RXD_RDY;
			default: p2_int_vector = 3'b000;
		endcase
	end
	localparam CFG_REQ = 1;
	localparam TX_DONE = 0;
	wire p3_enable_load;
	reg [1:0] p3_reset;
	reg [1:0] p3_int_bundle_CRT;
	wire [1:0] p3_int_bundle_NXT;
	genvar k;
	generate
		for (k = 0; k < 2; k = k + 1) begin : genblk3
			always @(posedge clk_i or negedge rst_n_i)
				if (!rst_n_i)
					p3_int_bundle_CRT[k] <= 1'b0;
				else if (p3_reset[k] | disable_interrupts_i)
					p3_int_bundle_CRT[k] <= 1'b0;
				else if (p3_enable_load)
					p3_int_bundle_CRT[k] <= p3_int_bundle_NXT[k];
		end
	endgenerate
	assign p3_int_bundle_NXT = {config_req_slv_i, tx_done};
	assign p3_enable_load = |p3_int_bundle_NXT;
	reg [2:0] p3_int_vector;
	localparam uart_pkg_INT_CONFIG_REQ = 3'b111;
	localparam uart_pkg_INT_TX_DONE = 3'b000;
	always @(*) begin : prio3_vector_gen
		casez (p3_int_bundle_NXT)
			2'b1z: p3_int_vector = uart_pkg_INT_CONFIG_REQ;
			2'b01: p3_int_vector = uart_pkg_INT_TX_DONE;
			default: p3_int_vector = 3'b000;
		endcase
	end
	localparam PRIORITY_1 = 3'bzz1;
	localparam PRIORITY_2 = 3'bz10;
	localparam PRIORITY_3 = 3'b100;
	wire [2:0] priority_select;
	assign priority_select[0] = |p1_int_bundle_NXT & !disable_interrupts_i;
	assign priority_select[1] = |p2_int_bundle_NXT & !disable_interrupts_i;
	assign priority_select[2] = |p3_int_bundle_NXT & !disable_interrupts_i;
	reg [2:0] state_CRT;
	reg [2:0] state_NXT;
	always @(posedge clk_i or negedge rst_n_i) begin : fsm_state_register
		if (!rst_n_i)
			state_CRT <= 3'd0;
		else if (disable_interrupts_i)
			state_CRT <= 3'd0;
		else
			state_CRT <= state_NXT;
	end
	reg interrupt_clear;
	reg interrupt_set;
	always @(posedge clk_i or negedge rst_n_i)
		if (!rst_n_i)
			ireq_n_o <= 1'b1;
		else if (interrupt_set)
			ireq_n_o <= 1'b0;
		else if (interrupt_clear)
			ireq_n_o <= 1'b1;
	reg [2:0] interrupt_vector;
	always @(*) begin : fsm_next_state_logic
		state_NXT = state_CRT;
		p1_reset = 4'b0000;
		p2_reset = 2'b00;
		p3_reset = 2'b00;
		interrupt_vector = 3'b000;
		store_int_vect_o = 1'b0;
		interrupt_set = 1'b0;
		interrupt_clear = 1'b0;
		casez (priority_select)
			PRIORITY_1: interrupt_vector = p1_int_vector;
			PRIORITY_2: interrupt_vector = p2_int_vector;
			PRIORITY_3: interrupt_vector = p3_int_vector;
			default: interrupt_vector = 3'b000;
		endcase
		case (state_CRT)
			3'd0:
				if (priority_select != 0) begin
					interrupt_set = 1'b1;
					store_int_vect_o = 1'b1;
					casez (priority_select)
						PRIORITY_1: state_NXT = 3'd1;
						PRIORITY_2: state_NXT = 3'd2;
						PRIORITY_3: state_NXT = 3'd3;
					endcase
				end
			3'd1: begin
				p1_reset = 4'b0000;
				p2_reset[RX_RDY] = 1'b0;
				case (interrupt_vector)
					uart_pkg_INT_CONFIG_FAIL:
						if (int_ackn_i) begin
							p1_reset[CFG_ERROR] = 1'b1;
							state_NXT = 3'd4;
							interrupt_clear = 1'b1;
						end
					uart_pkg_INT_OVERRUN, uart_pkg_INT_FRAME, uart_pkg_INT_PARITY:
						if (read_rx_data_i) begin
							p1_reset[OVR_ERROR] = 1'b1;
							p1_reset[FRM_ERROR] = 1'b1;
							p1_reset[PAR_ERROR] = 1'b1;
							p2_reset[RX_RDY] = 1'b1;
							state_NXT = 3'd4;
							interrupt_clear = 1'b1;
						end
				endcase
			end
			3'd2: begin
				p2_reset[RX_RDY] = 1'b1;
				p2_reset[RX_FULL] = 1'b1;
				if ((rx_dsm_i & rx_fifo_empty_i) | (!rx_dsm_i & read_rx_data_i)) begin
					case (interrupt_vector)
						uart_pkg_INT_RX_FULL: p2_reset[RX_FULL] = 1'b1;
						uart_pkg_INT_RXD_RDY: p2_reset[RX_RDY] = 1'b1;
					endcase
					state_NXT = 3'd5;
					interrupt_clear = 1'b1;
				end
			end
			3'd3: begin
				p3_reset[TX_DONE] = 1'b0;
				p3_reset[CFG_REQ] = 1'b0;
				case (interrupt_vector)
					uart_pkg_INT_CONFIG_REQ:
						if (request_ack_i) begin
							p3_reset[CFG_REQ] = 1'b1;
							interrupt_clear = 1'b1;
							state_NXT = 3'd6;
						end
					uart_pkg_INT_TX_DONE:
						if (int_ackn_i) begin
							p3_reset[TX_DONE] = 1'b1;
							interrupt_clear = 1'b1;
							state_NXT = 3'd6;
						end
				endcase
			end
			3'd4:
				if (p1_int_bundle_CRT != 0) begin
					state_NXT = 3'd1;
					interrupt_set = 1'b1;
				end
				else
					state_NXT = 3'd0;
			3'd5:
				if (p2_int_bundle_CRT != 0) begin
					state_NXT = 3'd2;
					interrupt_set = 1'b1;
				end
				else
					state_NXT = 3'd0;
			3'd6:
				if (p3_int_bundle_CRT != 0) begin
					state_NXT = 3'd3;
					interrupt_set = 1'b1;
				end
				else
					state_NXT = 3'd0;
		endcase
	end
	assign interrupt_vector_o = interrupt_vector;
endmodule
