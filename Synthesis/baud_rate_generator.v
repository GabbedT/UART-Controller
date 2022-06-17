module baud_rate_generator (
	clk_i,
	rst_n_i,
	divisor_i,
	ov_baud_rt_o
);
	input wire clk_i;
	input wire rst_n_i;
	input wire [15:0] divisor_i;
	output wire ov_baud_rt_o;
	reg [15:0] counter_ov;
	always @(posedge clk_i) begin : counter_16_br
		if (!rst_n_i)
			counter_ov <= 16'b0000000000000000;
		else
			counter_ov <= (counter_ov == divisor_i ? 16'b0000000000000000 : counter_ov + 1'b1);
	end
	assign ov_baud_rt_o = counter_ov == 1;
endmodule
