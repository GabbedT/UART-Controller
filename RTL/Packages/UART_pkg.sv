`ifndef UART_PACKAGE
  `define UART_PACKAGE

package UART_pkg;

//----------------------//
//  GENERAL PARAMETERS  //
//----------------------//

  /* System clock frequency in Hz */
  localparam SYSTEM_CLOCK_FREQ = 100_000_000;

  /* Number of words stored in the buffers */
  localparam TX_FIFO_DEPTH = 64;
  localparam RX_FIFO_DEPTH = 64;

  /* Interrupt id */
  localparam INT_TX_DONE     = 3'b000;
  localparam INT_CONFIG_FAIL = 3'b001;
  localparam INT_OVERRUN     = 3'b010;
  localparam INT_FRAME       = 3'b011;
  localparam INT_PARITY      = 3'b100;
  localparam INT_RXD_RDY     = 3'b101;
  localparam INT_RX_FULL     = 3'b110;
  localparam INT_CONFIG_REQ  = 3'b111;

  /* Communication mode */
  localparam DISABLED    = 2'b00;
  localparam SIMPLEX_TX  = 2'b01;
  localparam SIMPLEX_RX  = 2'b10;
  localparam FULL_DUPLEX = 2'b11;

  /* Number of SYN character received to detect the 
   * start of the configuration request */
  localparam SYN_NUMBER = 3;


//---------------//
//  DATA PACKET  //
//---------------//

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

  function logic [7:0] assemble_packet(input logic [1:0] id, input logic [1:0] option);
    return {4'b0, option, id};
  endfunction : assemble_packet

  /* ASCII synchronous idle character */
  localparam SYN = 8'h16;
  

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

//---------------------------//
//  ERROR AND CONFIGURATION  //
//---------------------------//


  /* Standard configuration */
  localparam STD_DATA_WIDTH  = DW_8BIT;
  localparam STD_STOP_BITS   = SB_1BIT;
  localparam STD_PARITY_MODE = EVEN;

  localparam STD_CONFIGURATION = {STD_DATA_WIDTH, STD_PARITY_MODE, STD_STOP_BITS};
  
  typedef struct packed {
    /* If the UART doesn't see a stop bit */
    logic frame;
    /* If the receiver's buffer is full and the UART
     * is receiving data */
    logic overrun;
    /* If parity doesn't match */
    logic parity;
    /* If the uart has recieved an illegal config packet */
    logic configuration;
  } uart_error_s;

  typedef struct packed {
    logic [1:0] data_width;
    logic [1:0] parity_mode;
    logic [1:0] stop_bits;
  } uart_config_s;


endpackage

`endif 
