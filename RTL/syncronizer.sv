module syncronizer #(parameter RESET_VALUE = 0) (
    input  logic clk_i,
    input  logic rst_n_i,
    input  logic async_sign_i,

    output logic sync_sign_o
);

    logic signal_ff;

    always_ff @(posedge clk_i or negedge rst_n_i) begin 
        if (!rst_n_i) begin
            {sync_sign_o, signal_ff} <= RESET_VALUE;
        end else begin
            {sync_sign_o, signal_ff} <= {signal_ff, async_sign_i};
        end
    end

endmodule : syncronizer