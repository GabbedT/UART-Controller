#ifndef UART_DEFINES_INCLUDED
#define UART_DEFINES_INCLUDED

//--------------//
//  PARAMETERS  //
//--------------//

/*
 *  Define the system clock here or include it with the same name.
 *  The system clock is used to calculate the desired baud rate.
 */
#define SYS_CLOCK_FREQ 1'000'000  /* 1MHz clock */

#define RX_FIFO_SIZE 64     /* In byte */
#define TX_FIFO_SIZE 64     /* In byte */

/* Used to store data */
#define RX_UART_BUFFER_SIZE 256   /* In byte */
#define TX_UART_BUFFER_SIZE 256   /* In byte */


//----------------//
//  INTERRUPT ID  //
//----------------//

#define INT_TX_DONE     0b000
#define INT_CONFIG_FAIL 0b001
#define INT_OVERRUN     0b010
#define INT_PARITY      0b011
#define INT_FRAME       0b100
#define INT_RXD_RDY     0b101
#define INT_RX_FULL     0b110
#define INT_CONFIG_REQ  0b111


//--------------------//
//  CONFIGURATION ID  //
//--------------------//

#define DATA_WIDTH_5 0
#define DATA_WIDTH_6 1
#define DATA_WIDTH_7 2
#define DATA_WIDTH_8 3

#define PARITY_EVEN 0
#define PARITY_ODD  1

#define DISABLE     0
#define SIMPLEX_TX  1
#define SIMPLEX_RX  2
#define FULL_DUPLEX 3

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
 *  [6]   | RX data stream mode enable                    | R / W       |
 *  [7]   | TX data stream mode enable                    | R / W       | 
 * -----------------------------------------------------------------------
 */

#define DATA_WIDTH          0x03
#define PARITY_MODE         0x0C
#define STOP_BITS           0x30
#define RX_DATA_STREAM_MODE 0x40
#define TX_DATA_STREAM_MODE 0x80


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
 *  [0]     | Acknowledge configuration request             | W           |
 *  [1]     | Set standard configuration                    | W           |
 *  [2]     | Configuration done                            | R           |
 *  [3]     | Enable configuration request                  | R / W       | 
 *  [5:4]   | Configure communication mode                  | R / W       |  
 *  [6]     | Interrupt pending                             | R           | 
 *  [7]     | Interrupt mode                                |           
 * -------------------------------------------------------------------------
 */

#define ACK_REQ        0x01
#define SET_STD_CONFIG 0x02
#define CFG_DONE       0x04
#define EN_CFG_REQ     0x08
#define COMM_MODE      0x30
#define INT_PENDING    0x40
#define INT_MODE       0x80


//----------------//
//  ISR REGISTER  //
//----------------//

/*
 *  ISR Register bit fields 
 * ----------------------------------------------------------------------------------------------------
 *  Bits   | Description                          | Access mode |                                    |
 * ----------------------------------------------------------------------------------------------------
 *  [2:0]  | Interrupt code                       | R           |                                    |
 *  [3]    | Overrun error interrupt enable       | W           |                                    |
 *  [4]    | Parity error interrupt enable        | W           |                                    |
 *  [5]    | Frame error interrupt enable         | W           |                                    |
 *  [6]    | Data rx ready interrupt enable       | W           |                                    |
 *  [7]    | Data tx ready interrupt enable       | W           |                                    | 
 * ----------------------------------------------------------------------------------------------------
 *  The interrupt has to be acknowledged in every case by writing a 1 to the interrupt acknowledge   |
 *  bit field.                                                                                       |
 * ----------------------------------------------------------------------------------------------------
 *  Cause                   | Priority | ID   | Clears                                               | 
 * ----------------------------------------------------------------------------------------------------
 *  Transmission done       | 3        | 000  | Acknowledge interrupt                                |
 * ----------------------------------------------------------------------------------------------------
 *  Configuration error     | 1        | 001  | Acknowledge interrupt                                |
 * ----------------------------------------------------------------------------------------------------
 *  Overrun error           | 1        | 010  | Read the data            	                         |
 * ----------------------------------------------------------------------------------------------------
 *  Frame error             | 1        | 011  | Read the data            	                         |
 * ----------------------------------------------------------------------------------------------------
 *  Parity error            | 1        | 100  | Read the data            	                         |
 * ----------------------------------------------------------------------------------------------------
 *  Data received ready     | 3        | 101  | Standard mode: read RXR.                             |
 *                          |          |      | Data stream mode: The fifo has reached his threshold |
 *                          |          |      | read RXR till the buffer is empty.                   |
 * ----------------------------------------------------------------------------------------------------
 *  Receiver fifo full      | 2        | 110  | Standard mode: read RXR.                             |
 *                          |          |      | Data stream mode: read RXR till the buffer is empty. | 
 * ----------------------------------------------------------------------------------------------------  
 *  Requested configuration | 2        | 111 | Acknowledge the request or let the request expire.    |
 * ----------------------------------------------------------------------------------------------------                        
 */

#define INT_ID        0x07
#define INT_OVR_EN    0x08
#define INT_PAR_EN    0x10
#define INT_FRM_EN    0x20
#define INT_RX_RDY_EN 0x40
#define INT_TX_RDY_EN 0x80


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