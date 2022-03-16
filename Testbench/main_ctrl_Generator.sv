`ifndef MAIN_CTRL_GENERATOR_SV
  `define MAIN_CTRL_GENERATOR_SV

class main_ctrl_Generator #(parameter TEST_NUMBER = 100, parameter DEBUG = 1);

    main_ctrl_Transaction trxPacket;

    /* Send randomized transactions to driver */
    mailbox gen2drv_mbx;

    /* Triggers when the generator has finished generating new transaction */
    event genDone_ev;

    /* Numer of transaction to generate */
    int trxGeneration;
    
    bit [1:0] parity_mode;

//-------------//
// CONSTRUCTOR //
//-------------//

    function new(input event genDone_ev, input mailbox gen2drv_mbx);
        this.gen2drv_mbx = gen2drv_mbx;
        this.genDone_ev = genDone_ev;
        this.trxGeneration = TEST_NUMBER;
    endfunction : new

//---------------//
// MAIN FUNCTION //
//---------------//

    task run();
        $display("[Generator] Starting...");

        repeat(trxGeneration) begin
            trxPacket = new(1);
            parity_mode = trxPacket.cfg.config_i.parity.option;

            assert(trxPacket.randomize())
            else $fatal("[Generator] Error on randomization");

            trxPacket.data.parity_i = trxPacket.data.calc_parity(parity_mode);

            if (DEBUG) begin
              trxPacket.data.displayData("Generator");
              trxPacket.cfg.displayConfig("Generator");
            end
            
            gen2drv_mbx.put(trxPacket);
        end
        
        ->genDone_ev;
    endtask : run 

endclass : main_ctrl_Generator

`endif 