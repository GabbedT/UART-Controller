`ifndef REGISTERS_PKG
  `define REGISTERS_PKG

package registers_pkg;

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
    logic       RESERVED;
    logic       INTPEND;
    logic [1:0] COM;
    logic       ENREQ;
    logic       CDONE;
    logic       AKREQ;
    logic       STDC;
  } CTR_data_t;


//----------------//
//  ISR REGISTER  //
//----------------//

  typedef struct packed {
    logic       RXRDY;
    logic       FRM;
    logic       PAR;
    logic       OVR;
    logic [2:0] INTID;
    logic       IACK;
  } ISR_data_t;


//------------------------//
//  TESTBENCH OPERATIONS  //
//------------------------//

  typedef enum int {
    /* Read STR */
    READ_CONFIG,

    /* Set RX threshold */
    SET_THRESHOLD,

    /* Set communication mode */
    SET_COM_MODE,

    /* Enable or disable configurations requests */
    ENABLE_CONFIG_REQ,

    /* Random enable interrupt */
    ENABLE_INTERRUPT,

    /* Read RXR */
    READ_DATA,

    /* Write TXR */
    SEND_DATA,

    /* Send a burst of data */
    SEND_DATA_BURST,

    /* Do nothing */
    NO_OPERATION
  } operation_t;

endpackage : registers_pkg

`endif 