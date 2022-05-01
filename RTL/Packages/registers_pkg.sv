`ifndef REGISTERS_PKG
  `define REGISTERS_PKG

package registers_pkg;

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
    logic [1:0] COM;
    logic       ENREQ;
    logic       CDONE;
    logic       AKREQ;
    logic       STDC;
    logic       SREQ;
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

endpackage : registers_pkg

`endif 