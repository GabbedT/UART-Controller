#ifndef UART_REGMAP_INCLUDED
#define UART_REGMAP_INCLUDED

//----------------//
//  STR REGISTER  //
//----------------//

/* 
 *  STR Register bit fields 
 * -------------------------------------------------------------------------
 *  Bits    | Description                                   | Access mode |
 * -------------------------------------------------------------------------
 *  [15:0]  | Divisor value to obtain the desired baud rate | R / W       |
 *  [17:16] | Data width configuration ID                   | R / W       |
 *  [19:18] | Parity configuration ID                       | R / W       | 
 *  [21:20] | Stop bits number configuration ID             | R / W       | 
 *  [22]    | Data stream mode enable                       | R / W       |
 *  [29:23] | Fifo rx interrupt threshold                   | R / W       |
 *  [31:30] | Reserved                                      | NONE        |
 * -------------------------------------------------------------------------
 */

#define DIVISOR             0x0000FFFF
#define DATA_WIDTH          0x00030000
#define PARITY_MODE         0x000C0000
#define STOP_BITS           0x00300000
#define DATA_STREAM_MODE    0x00400000
#define FIFO_THRESHOLD      0x3F800000


//----------------//
//  CTR REGISTER  //
//----------------//

/* 
 *  CTR Register bit fields 
 * -------------------------------------------------------------------------
 *  Bits    | Description                                   | Access mode |
 * -------------------------------------------------------------------------  
 *  [0]     | Configuration requested (SLAVE)               | R           |
 *  [1]     | Set standard configuration                    | W           |
 *  [2]     | Acknowledge configuration request             | W           |
 *  [3]     | Configuration done                            | R           |
 *  [31:4]  | Reserved                                      | NONE        |
 * -------------------------------------------------------------------------
 */

#define CFG_REQ_SLV  0x00000001
#define STD_CONFIG   0x00000002
#define ACKN_CFG     0x00000004
#define CFG_DONE     0x00000008


//----------------//
//  ISR REGISTER  //
//----------------//

/*
 *  ISR Register bit fields 
 * ----------------------------------------------------------------------------------------------------
 *  Bits   | Description               | Access mode |                                               |
 * ----------------------------------------------------------------------------------------------------
 *  [0]    | Interrupt pending         | R           |                                               |
 *  [2:1]  | Interrupt code            | R           |                                               |
 *  [3]    | Interrupt acknowledge     | W           |                                               |
 *  [31:4] | Reserved                  | NONE        |                                               |
 * ----------------------------------------------------------------------------------------------------
 *  The interrupt has to be acknowledged in every case by writing a 1 to the interrupt acknowledge   |
 *  bit field.                                                                                       |
 * ----------------------------------------------------------------------------------------------------
 *  Cause                   | Priority | ID   | Clears                                               | 
 * ----------------------------------------------------------------------------------------------------
 *  None                    | None     | 0000 | None                                                 |
 * ----------------------------------------------------------------------------------------------------
 *  Configuration error     | 1        | 0001 | Send another configuration request                   |
 * ----------------------------------------------------------------------------------------------------
 *  Overrun error           | 1        | 0010 | Read the data            	                         |
 * ----------------------------------------------------------------------------------------------------
 *  Parity error            | 1        | 0100 | Read the data            	                         |
 * ----------------------------------------------------------------------------------------------------
 *  Frame error             | 1        | 1000 | Read the data            	                         |
 * ----------------------------------------------------------------------------------------------------
 *  Data received ready     | 3        | 0011 | Standard mode: read RXR.                             |
 *                          |          |      | Data stream mode: The fifo has reached his threshold |
 *                          |          |      | read RXR till the buffer is empty.                   |
 * ----------------------------------------------------------------------------------------------------
 *  Receiver fifo full      | 2        | 0101 | Standard mode: read RXR.                             |
 *                          |          |      | Data stream mode: read RXR till the buffer is empty. | 
 * ----------------------------------------------------------------------------------------------------  
 *  Requested configuration | 2        | 0110 | Acknowledge the request or let the request expire.   |
 * ----------------------------------------------------------------------------------------------------                        
 */

#define INT_PEND 0x00000001
#define INT_ID   0x00000006
#define INT_ACKN 0x00000008


//----------------//
//  IMR REGISTER  //
//----------------//

/* 
 *  IMR Register bit fields 
 * ---------------------------------------------------------------
 *  Bits   | Description                          | Access mode |
 * ---------------------------------------------------------------
 *  [0]    | Overrun error interrupt enable       | W           |
 *  [1]    | Parity error interrupt enable        | W           |
 *  [2]    | Frame error interrupt enable         | W           |
 *  [3]    | Data rx ready interrupt enable       | W           |  
 *  [31:4] | Reserved                             | NONE        |
 * --------------------------------------------------------------- 
 */ 

#define INT_OVR_EN 0x00000001
#define INT_PAR_EN 0x00000002
#define INT_FRM_EN 0x00000004
#define INT_RXD_EN 0x00000008


//----------------//
//  RXR REGISTER  //
//----------------//

/* 
 *  RXR Register bit fields 
 * ----------------------------------------------------------------
 *  Bits    | Description                          | Access mode |
 * ----------------------------------------------------------------
 *  [7:0]   | Received data                        | R           |
 *  [8]     | FIFO RX full                         | R           |
 *  [9]     | FIFO RX empty                        | R           |
 *  [31:10] | Reserved                             | NONE        |
 * ----------------------------------------------------------------
 */

#define DATA_RX  0x000000FF
#define RX_FULL  0x00000100
#define RX_EMPTY 0x00000200


//----------------//
//  TXR REGISTER  //
//----------------//

/* 
 *  TXR Register bit fields 
 * ----------------------------------------------------------------
 *  Bits    | Description                          | Access mode |
 * ----------------------------------------------------------------
 *  [7:0]   | Data to be send                      | W           |
 *  [8]     | FIFO TX full                         | R           |
 *  [9]     | FIFO TX empty                        | R           |
 *  [31:10] | Reserved                             | NONE        |
 * ----------------------------------------------------------------
 */ 

#define DATA_TX  0x000000FF
#define TX_FULL  0x00000100
#define TX_EMPTY 0x00000200  


//----------------//
//  IFR REGISTER  //
//----------------//

/* 
 *  IFR Register bit fields 
 * -----------------------------------------------------------------
 *  Bits    | Description                           | Access mode |
 * -----------------------------------------------------------------
 *  [15:0]  | Creator's device initials (GT) in hex | R           |
 *  [23:16] | Product number                        | R           |
 *  [31:24] | Device's number in the system         | R           | 
 * -----------------------------------------------------------------  
 */

#define DEVICE_INITIALS 0x0000FFFF
#define PRODUCT_NUMBER  0x00FF0000
#define DEVICE_NUMBER   0xFF000000

#endif