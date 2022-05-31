import registers_pkg::*;

module uart_test ();

    bit        clk_i = 1'b0;
    bit        rst_n_i = 1'b1;
    bit        chip_sel_n_i = 1'b1;
    bit [2:0]  address_i;
    bit        read_write_i;
    wire [7:0] data_io;
    bit        rx_i;
    bit        tx_o;
    bit        ireq_n_o;

    bit [7:0] data_wr;
    bit [7:0] data_rd;
    assign data_io = (!read_write_i & !chip_sel_n_i) ? data_wr : 8'bZ;

    always #10 clk_i <= !clk_i;


//---------//
//  TASKS  //
//---------//

    task uart_enable_chip();
        chip_sel_n_i = 1'b0;
    endtask : enable_chip

    task uart_disable_chip();
        chip_sel_n_i = 1'b1;
    endtask : disable_chip

    task uart_write(input bit [7:0] data, input bit [2:0] address);
        data_wr <= data;
        address_i <= address;
        read_write_i <= 1'b0;
        uart_enable_chip();
        @(posedge clk_i);
        uart_disable_chip();
        @(posedge clk_i);
    endtask : write

    task uart_read(output bit [7:0] data, input bit [2:0] address);
        address_i <= address;
        read_write_i <= 1'b1;
        uart_enable_chip();
        @(posedge clk_i);
        data <= data_io;
        uart_disable_chip();
        @(posedge clk_i);
    endtask : read 

    task uart_send_string(input string str);
        if (str.len() > TX_FIFO_DEPTH) begin 
            $display("String too long")
        end 

        for(int i = 0; i < str.len; ++i) begin 
            write(string_uart2rcv[i], TXR_ADDR);
        end
    endtask : send_string

    task uart_isr();

    endtask : uart_isr


//-------//
//  DUT  //
//-------//

    uart dut (.*);

    string    string_uart2rcv = "Hi, this is the DUT. I hope you received the message!";
    string    string_tx2uart = "Hi, this is the transmitter, I hope you received the message!";


//-----------------//
//  BAUD RATE GEN  //
//-----------------//

    bit [15:0] divisor_i = 16'd26;
    bit        ov_baud_rt_o;

    baud_rate_generator bd_gen (.*);


//------------//
//  RECEIVER  //
//------------//

    bit       rcv_read = 1'b0;
    bit       rcv_idle;
    bit [7:0] data_rcv;
    bit [7:0] string_rcv[64];
    bit       rx_fifo_empty;

    receiver rx (
        .clk_i                  ( clk_i           ),
        .rst_n_i                ( rst_n_i         ),
        .enable                 ( 1'b1            ),
        .ov_baud_rt_i           ( ov_baud_rt_o    ),
        .rx_i                   ( tx_o            ),
        .rx_fifo_read_i         ( rcv_read        ),
        .req_ackn_i             ( 1'b0            ),
        .threshold_i            ( 6'b0            ),
        .rx_data_stream_mode_i  ( 1'b0            ),
        .data_width_i           ( STD_DATA_WIDTH  ),
        .stop_bits_number_i     ( STD_STOP_BITS   ),
        .parity_mode_i          ( STD_PARITY_MODE ),
        .rx_fifo_full_o         (                 ),
        .rx_fifo_empty_o        ( rx_fifo_empty   ),
        .config_req_slv_o       (                 ),
        .overrun_error_o        (                 ),
        .frame_error_o          (                 ),
        .parity_o               (                 ),
        .rx_done_o              (                 ),
        .rxd_rdy_o              (                 ),
        .data_rx_o              ( data_rcv        ),
        .rx_idle_o              ( rcv_idle        )
    );


//---------------//
//  TRANSMITTER  //
//---------------//

    bit [7:0] data_tx2uart;
    bit       tx_write = 1'b0;
    bit       tx_idle;

    transmitter tx (
        .clk_i                  ( clk_i           ),
        .rst_n_i                ( rst_n_i         ),
        .enable                 ( 1'b1            ),
        .ov_baud_rt_i           ( ov_baud_rt_o    ),
        .data_tx_i              ( data_tx2uart    ),
        .tx_fifo_write_i        ( tx_write        ),
        .config_req_mst_i       ( 1'b0            ),
        .config_req_slv_i       ( 1'b0            ),
        .tx_data_stream_mode_i  ( 1'b0            ),
        .data_width_i           ( STD_DATA_WIDTH  ),
        .stop_bits_number_i     ( STD_STOP_BITS   ),
        .parity_mode_i          ( STD_PARITY_MODE ),
        .tx_o                   ( rx_i            ),
        .tx_done_o              (                 ),      
        .req_done_o             (                 ),
        .tx_fifo_empty_o        (                 ),
        .tx_fifo_full_o         (                 ),
        .tx_idle_o              ( tx_idle         )
    );


//-------------//
//  TESTBENCH  //
//-------------//

    bit gm_rx_done = 0;
    bit gm_tx_done = 0;
    int idx = 0;

    initial begin
        @(posedge clk_i);
        rst_n_i <= 1'b0;
        repeat(2) @(posedge clk_i);
        rst_n_i <= 1'b1;

        repeat(20) @(posedge clk_i);

        uart_write(divisor_i[7:0], LDVR_ADDR);
        uart_write(divisor_i[15:8], UDVR_ADDR);

        fork
            begin : gm_tx_port
                foreach(string_tx2uart[i]) begin 
                    data_tx2uart <= string_tx2uart[i];
                    tx_write <= 1'b1;
                    @(posedge clk_i);
                    tx_write <= 1'b0;
                    wait(tx_idle);
                end
                gm_tx_done <= 1'b1;
            end : gm_tx_port

            begin : gm_rx_port
                foreach(string_rcv[i]) begin  
                    wait (!rx_fifo_empty & rcv_idle);
                    rcv_read <= 1'b1;
                    string_rcv[i] <= data_rcv;
                    @(posedge clk_i);
                    rcv_read <= 1'b0;
                end
                gm_rx_done <= 1'b1;
            end : gm_rx_port

            begin : dut_tx_port
                foreach(string_uart2rcv[i]) begin 
                    uart_write(string_uart2rcv[i], TXR_ADDR);
                end
            end : dut_tx_port

            begin : dut_rx_port 
                while(!(gm_tx_done | gm_rx_done)) begin 
                    wait(!ireq_n_o);
                    uart_read(data_rd, ISR_ADDR);

                    if (data_rd[3:1] == INT_TX_DONE) begin 
                        uart_write({data_rd[7:1], 1'b1}, ISR_ADDR);
                    end else if (data_rd[3:1] == INT_RXD_RDY) begin 
                        uart_read(string_rcv[idx], RXR_ADDR);
                        ++idx;
                    end else begin 
                        $display("Error!");
                    end
                end
            end : dut_rx_port
        join

        $finish;
    end

endmodule : uart_test