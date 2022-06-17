module edge_detector (
	clk_i,
	signal_i,
	edge_pulse_o
);
	parameter EDGE = 1;
	input wire clk_i;
	input wire signal_i;
	output wire edge_pulse_o;
	reg signal_dly;
	always @(posedge clk_i) begin : delay
		signal_dly <= signal_i;
	end
	generate
		if (EDGE) begin : genblk1
			assign edge_pulse_o = signal_i & !signal_dly;
		end
		else begin : genblk1
			assign edge_pulse_o = !signal_i & signal_dly;
		end
	endgenerate
endmodule
