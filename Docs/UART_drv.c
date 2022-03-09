#ifndef UART_INCLUDED
#define UART_INCLUDED

#include <stdint.h>
#include <stdbool.h>
#include <stdlib.h>

/*
 *  Define the system clock here or include it with the same name.
 *  The system clock is used to calculate the desired baud rate.
 */
#define SYS_CLOCK_FREQ 100'000'000  /*  100MHz clock  */

/*
 *  Number of devices in the system 
 */
#define DEVICES_NUMBER 1


//----------------//
//  REGISTER MAP  //
//----------------//

/* Register addresses */

#define STR  0       /*  Status Register            */
#define CFR  1       /*  Configuration Register     */
#define ISR  2       /*  Interrupt Status Register  */
#define IMR  3       /*  Interrupt Mask Register    */
#define RXR  4       /*  RX Register                */
#define TXR  5       /*  TX Register                */
#define IFR  6       /*  Info Register              */

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
 *  [31:23] | Reserved                                      | NONE        |
 * -------------------------------------------------------------------------
 */

typedef union {
    uint32_t word;

    struct {
        uint16_t divisor;
        uint32_t dataWidth      : 2;
        uint32_t parityMode     : 2;
        uint32_t stopBitsNumber : 2;
        uint32_t dataStream     : 1;
    } field;
} volatile uartSTR_t;


/* 
 *  CFR Register bit fields 
 * -------------------------------------------------------------------------
 *  Bits    | Description                                   | Access mode |
 * ------------------------------------------------------------------------- 
 *  [0]     | Configuration request (MASTER)                | W           | 
 *  [1]     | Configuration requested (SLAVE)               | R           |
 *  [2]     | Set standard configuration                    | W           |
 *  [3]     | Acknowledge configuration request             | W           |
 *  [31:27] | Reserved                                      | NONE        |
 * -------------------------------------------------------------------------
 */

typedef union {
    uint32_t word;

    struct {
        uint32_t configReqMst  : 1;
        uint32_t configReqSlv  : 1;
        uint32_t setStdConfig  : 1;
        uint32_t acknConfigReq : 1;
    } field;
} volatile uartCFR_t;


/*
 *  ISR Register bit fields 
 * ---------------------------------------------------------------------------------------------------
 *  Bits   | Description               | Access mode |                                              |
 * ---------------------------------------------------------------------------------------------------
 *  [0]    | Interrupt pending         | NONE        |                                              |
 *  [2:1]  | Interrupt code            | R           |                                              |
 *  [31:4] | Reserved                  | NONE        |                                              |
 * ----------------------------------------------------------------------------------------------------
 *  Cause                   | Priority | ID   | Clears                                               | 
 * ----------------------------------------------------------------------------------------------------
 *  None                    | None     | 0000 | None                                                 |
 * ----------------------------------------------------------------------------------------------------
 *  Configuration error     | 1        | 0001 | Send another configuration request                   |
 * ----------------------------------------------------------------------------------------------------
 *  Overrun error           | 1        | 0010 | Read the data            	                         |
 * ----------------------------------------------------------------------------------------------------
 *  Parity error            | 1        | 0011 | Read the data            	                         |
 * ----------------------------------------------------------------------------------------------------
 *  Frame error             | 1        | 0100 | Read the data            	                         |
 * ----------------------------------------------------------------------------------------------------
 *  Data received ready     | 3        | 0101 | Standard mode: read RXR.                             |
 *                          |          |      | Data stream mode: read RXR till the buffer is empty. |
 * ----------------------------------------------------------------------------------------------------
 *  Receiver fifo full      | 2        | 0110 | Standard mode: read RXR.                             |
 *                          |          |      | Data stream mode: read RXR till the buffer is empty. | 
 * ----------------------------------------------------------------------------------------------------  
 *  Configuration done      | 3        | 0111 | Deassert one of the two config request bit in CFR.   |
 * ----------------------------------------------------------------------------------------------------
 *  Requested configuration | 2        | 1000 | Acknowledge the request or let the request expire.   |
 * ----------------------------------------------------------------------------------------------------                        
 */

typedef union {
    uint32_t word;

    struct {
        uint32_t intPending : 1;
        uint32_t intID      : 4;
    } field;
} volatile uartISR_t;


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

typedef union {
    uint32_t word;

    struct {
        uint32_t overrunIntEn : 1;
        uint32_t parityIntEn  : 1;
        uint32_t frameIntEn   : 1;
        uint32_t dataRdyIntEn : 1;
    } field;
} volatile uartIMR_t;


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

typedef union {
    uint32_t word;

    struct {
        uint8_t  rxData;
        uint32_t full  : 1;
        uint32_t empty : 1;
    } field;
} volatile uartRXR_t;


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

typedef union {
    uint32_t word;

    struct {
        uint8_t  txData;
        uint32_t full  : 1;
        uint32_t empty : 1;
    } field;
} volatile uartTXR_t;
         

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

typedef union {
    uint32_t word;

    struct {
        uint16_t initials;
        uint8_t  prodNumber;
        uint8_t  deviceID;
    } field;
} const uartIFR_t;


//---------------//
//  ENUMERATIONS //
//---------------//

    /* Interrupt code */
    typedef enum {
        INT_NONE = 0,
        INT_CONFIG_FAIL = 1,
        INT_OVERRUN = 2,
        INT_PARITY = 3,
        INT_FRAME = 4,
        INT_RXD_RDY = 5,
        INT_RX_FULL = 6,
        INT_CONFIG_DONE = 7,
        INT_CONFIG_REQ = 8
    } uartInterruptID_t;

    /*  Data width configuration code  */
    typedef enum {
        DATA_WIDTH_5 = 0,
        DATA_WIDTH_6 = 1,
        DATA_WIDTH_7 = 2,
        DATA_WIDTH_8 = 3
    } uartDataWidth_t;

    /*  Stop bits number configuration code  */
    typedef enum {
        STOP_BITS_1 = 0,
        STOP_BITS_RESERVED1 = 1,
        STOP_BITS_RESERVED2 = 2,
        STOP_BITS_2 = 3
    } uartStopBits_t;

    /*  Parity mode configuration code  */
    typedef enum {
        PARITY_DISABLED_1 = 0,
        PARITY_EVEN = 1,
        PARITY_DISABLED_2 = 2,
        PARITY_ODD = 3
    } uartParityMode_t;
    

//----------//
//  DEVICE  //
//----------//

/* Struct that rapresent the register map of the device */
static typedef struct {
    uartSTR_t str;
    uartCFR_t cfr;
    uartISR_t isr;
    uartIMR_t imr;
    uartRXR_t rxr;
    uartTXR_t txr;
    uartIFR_t ifr;
} uart_t;

/* Used to refer to a particular uart device. */ 
static uart_t *g_uart[DEVICES_NUMBER];


//------------------//
//  INITIALIZATION  //
//------------------//

/*
 *  Initialize the device specified by @devNumber with the address specified by @address.
 *  in this case the device is initialized with the standard configuration.
 */
void uart_init(uint32_t devNumber, uint32_t address);

/*
 *
 */
void uart_initParams(uint32_t devNumber, uint32_t address, uint32_t baudRate);


#endif
