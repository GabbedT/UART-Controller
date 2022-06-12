`ifndef UART_PKG_INCLUDED
    `define UART_PKG_INCLUDED

package uart_pkg;

//============================//
//  CONFIGURATION PARAMETERS  //
//============================//

    /* System clock frequency in Hz */
    localparam SYSTEM_CLOCK_FREQ = 50_000_000;

    /* Number of words stored in the buffers */
    localparam TX_FIFO_DEPTH = 64;
    localparam RX_FIFO_DEPTH = 64;

    /* Standard baud rate */
    localparam STD_BAUD_RATE = 9600;

    /* Define ISR vector placed on the bus in 
     * vectored interrupt mode */
    localparam UART_ISR_VECTOR = 8'hFF;


//===========================//
//  GENERAL UART PARAMETERS  //
//===========================//

//------------------------------//
//  PACKET WIDTH CONFIGURATION  //
//------------------------------//

    /* Command ID */
    localparam logic [1:0] DATA_WIDTH_ID = 2'b01;

    /* Configuration code */
    localparam logic [1:0] DW_5BIT = 2'b00;
    localparam logic [1:0] DW_6BIT = 2'b01;
    localparam logic [1:0] DW_7BIT = 2'b10;
    localparam logic [1:0] DW_8BIT = 2'b11;


//-----------------------------//
//  PARITY MODE CONFIGURATION  //
//-----------------------------//

    /* Command ID */
    localparam logic [1:0] PARITY_MODE_ID = 2'b10;

    /* Configuration code */
    localparam logic [1:0] EVEN       = 2'b00;
    localparam logic [1:0] ODD        = 2'b01;
    localparam logic [1:0] DISABLED1  = 2'b10;
    localparam logic [1:0] DISABLED2  = 2'b11;


//---------------------------//
//  STOP BITS CONFIGURATION  //
//---------------------------// 

    /* Command ID */
    localparam logic [1:0] STOP_BITS_ID = 2'b11;
    
    /* Configuration code */
    localparam logic [1:0] SB_1BIT   = 2'b00;
    localparam logic [1:0] SB_2BIT   = 2'b01;
    localparam logic [1:0] RESERVED1 = 2'b10;
    localparam logic [1:0] RESERVED2 = 2'b11;


//-----------------------------//
//  END CONFIGURATION PROCESS  //
//-----------------------------//

    localparam logic [1:0] END_CONFIGURATION_ID = 2'b00;


//-------------//
//  INTERRUPT  //
//-------------//

    /* Interrupt id */
    localparam INT_TX_DONE     = 3'b000;
    localparam INT_CONFIG_FAIL = 3'b001;
    localparam INT_OVERRUN     = 3'b010;
    localparam INT_FRAME       = 3'b011;
    localparam INT_PARITY      = 3'b100;
    localparam INT_RXD_RDY     = 3'b101;
    localparam INT_RX_FULL     = 3'b110;
    localparam INT_CONFIG_REQ  = 3'b111;

    /* Interrupt response mode */
    localparam NORMAL       = 2'b00;
    localparam FAST_CLEAR   = 2'b01;


//----------------------//
//  COMMUNICATION MODE  //
//----------------------//

    /* Communication mode */
    localparam DISABLED    = 2'b00;
    localparam SIMPLEX_TX  = 2'b01;
    localparam SIMPLEX_RX  = 2'b10;
    localparam FULL_DUPLEX = 2'b11;

    localparam STD_COMM_MODE = FULL_DUPLEX;


//----------------------//
//  GENERAL PARAMETERS  //
//----------------------//

    /* Next and current state */
    localparam NXT = 1;
    localparam CRT = 0;

    /* ASCII synchronous idle character */
    localparam SYN = 8'h16;

    /* Acknowledge packet */
    localparam ACKN_PKT = 8'hFF;

    /* Number of SYN character received to detect the 
    * start of the configuration request */
    localparam SYN_NUMBER = 3;

    /* Standard configuration */
    localparam STD_DATA_WIDTH = DW_8BIT;
    localparam STD_STOP_BITS = SB_1BIT;
    localparam STD_PARITY_MODE = EVEN;

    localparam STD_CONFIGURATION = {STD_STOP_BITS, STD_PARITY_MODE, STD_DATA_WIDTH};

    localparam STD_DIVISOR = int'((SYSTEM_CLOCK_FREQ / (16 * STD_BAUD_RATE)) - 1);


//----------------------//
//  MODULES PARAMETERS  //
//----------------------//

    /* How many clock cycles does it need to reach 1 ms 
     * based on a specific system clock */
    localparam COUNT_1MS = SYSTEM_CLOCK_FREQ / 1000;

    localparam READ = 1;
    localparam WRITE = 0;


//=========================//
//  REGISTERS DEFINITIONS  //
//=========================//

    /* Registers addresses */
    localparam STR_ADDR  = 0;
    localparam LDVR_ADDR = 1;
    localparam UDVR_ADDR = 2;
    localparam FSR_ADDR  = 3;
    localparam CTR_ADDR  = 4;
    localparam ISR_ADDR  = 5;
    localparam RXR_ADDR  = 6;
    localparam TXR_ADDR  = 7;

    /* Enable registers typedef */
    typedef struct packed {
        logic TXR;
        logic ISR;
        logic CTR;
        logic FSR;
        logic UDVR;
        logic LDVR;
        logic STR;
    } reg_enable_t;


//----------------//
//  STR REGISTER  //
//----------------//

    typedef struct packed {
        logic       TDSM;
        logic       RDSM;
        logic [1:0] SBID;
        logic [1:0] PMID;
        logic [1:0] DWID;
    } STR_data_t;


//----------------//
//  FSR REGISTER  //
//----------------//  

    typedef struct packed {
        logic       TXF;
        logic       RXE;
        logic [5:0] RX_TRESHOLD;
    } FSR_data_t;


//----------------//
//  CTR REGISTER  //
//----------------//

    typedef struct packed {
        logic       VECTORED;
        logic       INTPEND;
        logic [1:0] COM;
        logic       ENREQ;
        logic       CDONE;
        logic       STDC;
    } CTR_data_t;


//----------------//
//  ISR REGISTER  //
//----------------//

    typedef struct packed {
        logic       TXDONE;
        logic       RXRDY;
        logic       FRM;
        logic       PAR;
        logic       OVR;
        logic [2:0] INTID;
    } ISR_data_t;



//===================//
//  CONTROLLER UNIT  //
//===================//

    /* How many clock cycles does it need to reach 10 ms  
     * based on a specific system clock */
    localparam COUNT_10MS = SYSTEM_CLOCK_FREQ / 100;

    /*
     * Normally the data packet is just composed by 8 bit of data.
     * Data packet received from UART Host to CONFIGURE the device. 
     * is composed by 3 parts:
     *
     * COMMAND ID: bits [1:0] specifies the setting to configure
     * OPTION:     bits [3:2] select an option
     * DON'T CARE: bits [7:4] those bits are simply ignored
     */
    typedef struct packed {
        logic [3:0] dont_care;
        logic [1:0] option;
        logic [1:0] id;
    } configuration_packet_s;


    /* The packet can have 2 different rapresentation thus it's expressed as union */
    typedef union packed {
        /* Main state */
        logic [7:0] packet;
        /* Configuration state */
        configuration_packet_s cfg_packet;
    } data_packet_u;


    typedef struct packed {
        logic [1:0] data_width;
        logic [1:0] parity_mode;
        logic [1:0] stop_bits;
    } uart_config_s;


    function logic [7:0] assemble_packet(input logic [1:0] id, input logic [1:0] option);
        return {4'b0, option, id};
    endfunction : assemble_packet



//===================//
//  FSM DEFINITIONS  //
//===================//

//----------------//
//  CONTROL UNIT  //
//----------------//

    typedef enum logic [3:0] {
        /*
        * Send configuration request to slave device 
        */ 
        CFG_REQ_MST,

        /* 
        * If the device sees the initialization signal (10ms RX low) then send an acknowledgment packet 
        */
        SEND_ACKN_SLV,

        /* 
        * Drive TX low to send the initialization signal 
        */
        WAIT_CFG_PKT_SLV,

        /* 
        * Send configuration packets
        */ 
        SEND_CFG_PKT_MST,

        /* 
        * Wait transmitter to end the request or a configuration
        */
        WAIT_TX_MST,

        /*
        * Wait transmitter to end sending acknowledgment packet 
        */
        WAIT_TX_SLV,

        /* 
        * Wait request acknowledgment 
        */
        WAIT_REQ_ACKN_MST,

        /* 
        * Wait for the slave acknowledgment for the configuration packet received
        */
        WAIT_ACKN_MST,

        /*
        * Set the device in standard configuration
        */
        STD_CONFIG,

        /* 
        * UART's main state 
        */
        MAIN
    } main_control_fsm_e;


//------------//
//  RECEIVER  //
//------------//

    /* TX line in idle state */
    localparam RX_LINE_IDLE = 1;

    typedef enum logic [2:0] {
        /* 
        * The device is waiting for data
        */
        RX_IDLE,

        /* 
        * The device is receiving a configuration request 
        */

        RX_CONFIG_REQ,

        /* 
        * Sample start bit 
        */
        RX_START,

        /* 
        * Sample the data bits
        */
        RX_SAMPLE,

        /* 
        * Sample parity bit 
        */
        RX_PARITY,

        /* 
        * Sample stop bits to end the transaction 
        */
        RX_DONE
    } receiver_fsm_e;


//---------------//
//  TRANSMITTER  //
//---------------//

    /* TX line in idle state */
    localparam TX_LINE_IDLE = 1;

    typedef enum logic [2:0] {
        /*
        * The device is waiting for data 
        */
        TX_IDLE,

        /* 
        * Send a configuration request 
        */
        TX_CFG_REQ,

        /* 
        * Inform the other device that data is arriving
        * by sending a start bit 
        */
        TX_START,

        /* 
        * Transmit the data bits serially to the other device
        */
        TX_DATA,

        /* 
        * Transmit parity bit 
        */
        TX_PARITY,

        /* 
        * Send stop bits to end the transaction 
        */
        TX_DONE
    } transmitter_fsm_e;


//---------------------//
//  INTERRUPT ARBITER  //
//---------------------//

    typedef enum logic [2:0] {
        IDLE,

        /* Wait interrupt to be cleared */
        PRIO1_WAIT_ACKN,
        PRIO2_WAIT_ACKN,
        PRIO3_WAIT_ACKN,
        
        /* IRQ should stay low for at least 1 clock cycle */
        PRIO1_CLEAR,
        PRIO2_CLEAR,
        PRIO3_CLEAR
    } normal_interrupt_response_fsm_e;

endpackage : uart_pkg

/* Import automatically with include */
import uart_pkg::*;

`endif