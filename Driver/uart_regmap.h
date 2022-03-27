#ifndef UART_REGMAP_INCLUDED
#define UART_REGMAP_INCLUDED

//----------------//
//  REGISTER MAP  //
//----------------//

/* Register addresses */

#define STR_ADDR   0       /*  Status Register            */
#define LDVR_ADDR  1       /*  Lower Divisor Register     */
#define UDVR_ADDR  1       /*  Upper Divisor Register     */
#define FSR_ADDR   2       /*  Fifo Status Register       */       
#define CTR_ADDR   4       /*  Control Register           */
#define ISR_ADDR   5       /*  Interrupt Status Register  */
#define RXR_ADDR   6       /*  Data Received Register     */
#define TXR_ADDR   7       /*  Data Transmitted Register  */


//----------------//
//  STR REGISTER  //
//----------------//

/* 
 *  STR Register bit fields 
 * -----------------------------------------------------------------------
 *  Bits  | Description                                   | Access mode |
 * -----------------------------------------------------------------------
 *  [1:0] | Data width configuration ID                   | R / W       |
 *  [3:2] | Parity configuration ID                       | R / W       | 
 *  [5:4] | Stop bits number configuration ID             | R / W       | 
 *  [6]   | Data stream mode enable                       | R / W       |
 *  [7]   | Interrupt acknowledge                         | W           | 
 * -----------------------------------------------------------------------
 */

#define DATA_WIDTH          0x03
#define PARITY_MODE         0x0C
#define STOP_BITS           0x30
#define DATA_STREAM_MODE    0x40
#define INT_ACKN            0x80


//----------------//
//  DVR REGISTER  //
//----------------//

/* 
 *  DVR Register bit fields 
 * -------------------------------------------------------------------------
 *  Bits    | Description                                   | Access mode |
 * -------------------------------------------------------------------------
 *  [15:0]  | Divisor value to obtain the desired baud rate.| R / W       |
 *          | Since registers are 8 bit the lower and the   |             |
 *          | upper portions are addressed differently      |             |
 * -------------------------------------------------------------------------
 */

#define LOWER_DIVISOR 0x00FF
#define UPPER_DIVISOR 0xFF00


//----------------//
//  FSR REGISTER  //
//----------------//

/* 
 *  FSR Register bit fields 
 * -------------------------------------------------------------------------
 *  Bits    | Description                                   | Access mode |
 * -------------------------------------------------------------------------
 *  [5:0]   | Fifo RX interrupt threshold                   | R / W       |
 *  [6]     | FIFO RX empty                                 | R           |
 *  [7]     | FIFO TX full                                  | R           |
 * -------------------------------------------------------------------------
 */

#define FIFO_THRESHOLD 0x3F
#define RX_EMPTY       0x40
#define TX_FULL        0x80


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
 * -------------------------------------------------------------------------
 */

#define CFG_REQ_SLV  0x01
#define STD_CONFIG   0x02
#define ACKN_CFG     0x04
#define CFG_DONE     0x08


//----------------//
//  ISR REGISTER  //
//----------------//

/*
 *  ISR Register bit fields 
 * ----------------------------------------------------------------------------------------------------
 *  Bits   | Description                          | Access mode |                                    |
 * ----------------------------------------------------------------------------------------------------
 *  [0]    | Interrupt pending                    | R           |                                    |
 *  [3:1]  | Interrupt code                       | R           |                                    |
 *  [4]    | Overrun error interrupt enable       | W           |                                    |
 *  [5]    | Parity error interrupt enable        | W           |                                    |
 *  [6]    | Frame error interrupt enable         | W           |                                    |
 *  [7]    | Data rx ready interrupt enable       | W           |                                    |
 * ----------------------------------------------------------------------------------------------------
 *  The interrupt has to be acknowledged in every case by writing a 1 to the interrupt acknowledge   |
 *  bit field.                                                                                       |
 * ----------------------------------------------------------------------------------------------------
 *  Cause                   | Priority | ID   | Clears                                               | 
 * ----------------------------------------------------------------------------------------------------
 *  None                    | None     | 000  | None                                                 |
 * ----------------------------------------------------------------------------------------------------
 *  Configuration error     | 1        | 001  | Send another configuration request                   |
 * ----------------------------------------------------------------------------------------------------
 *  Overrun error           | 1        | 010  | Read the data            	                           |
 * ----------------------------------------------------------------------------------------------------
 *  Parity error            | 1        | 011  | Read the data            	                           |
 * ----------------------------------------------------------------------------------------------------
 *  Frame error             | 1        | 100  | Read the data            	                           |
 * ----------------------------------------------------------------------------------------------------
 *  Data received ready     | 3        | 101  | Standard mode: read RXR.                             |
 *                          |          |      | Data stream mode: The fifo has reached his threshold |
 *                          |          |      | read RXR till the buffer is empty.                   |
 * ----------------------------------------------------------------------------------------------------
 *  Receiver fifo full      | 2        | 110  | Standard mode: read RXR.                               |
 *                          |          |      | Data stream mode: read RXR till the buffer is empty. | 
 * ----------------------------------------------------------------------------------------------------  
 *  Requested configuration | 2        | 111 | Acknowledge the request or let the request expire.    |
 * ----------------------------------------------------------------------------------------------------                        
 */

#define INT_PEND   0x01
#define INT_ID     0x0E
#define INT_OVR_EN 0x10
#define INT_PAR_EN 0x20
#define INT_FRM_EN 0x40
#define INT_RXD_EN 0x80


//----------------//
//  RXR REGISTER  //
//----------------//

/* 
 *  RXR Register bit fields 
 * ----------------------------------------------------------------
 *  Bits    | Description                          | Access mode |
 * ----------------------------------------------------------------
 *  [7:0]   | Received data                        | R           |
 * ----------------------------------------------------------------
 */

#define DATA_RX  0xFF


//----------------//
//  TXR REGISTER  //
//----------------//

/* 
 *  TXR Register bit fields 
 * ----------------------------------------------------------------
 *  Bits    | Description                          | Access mode |
 * ----------------------------------------------------------------
 *  [7:0]   | Data to be send                      | W           |
 * ----------------------------------------------------------------
 */ 

#define DATA_TX  0xFF

#endif