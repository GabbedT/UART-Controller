#ifndef UART_HEADER_INCLUDED
#define UART_HEADER_INCLUDED

#include <stdint.h>
#include <stdbool.h>
#include <stdlib.h>

/*
 *  Define the system clock here or include it with the same name.
 *  The system clock is used to calculate the desired baud rate.
 */
#define SYS_CLOCK_FREQ 100'000'000  /*  100MHz clock  */

#define RX_FIFO_SIZE 64     /* In byte */
#define TX_FIFO_SIZE 64     /* In byte */


//---------------//
//  ENUMERATIONS //
//---------------//

    /* Interrupt code */
    typedef enum {
        INT_NONE = 0b000,
        INT_CONFIG_FAIL = 0b001,
        INT_OVERRUN = 0b010,
        INT_PARITY = 0b011,
        INT_FRAME = 0b100,
        INT_RXD_RDY = 0b101,
        INT_RX_FULL = 0b110,
        INT_CONFIG_REQ = 0b111
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
        STOP_BITS_2 = 1,
        STOP_BITS_RESERVED1 = 2,
        STOP_BITS_RESERVED2 = 3
    } uartStopBits_t;

    /*  Parity mode configuration code  */
    typedef enum {
        PARITY_EVEN = 0,
        PARITY_ODD = 1,
        PARITY_DISABLED_1 = 2,
        PARITY_DISABLED_2 = 3
    } uartParityMode_t;
    


//----------//
//  DEVICE  //
//----------//

/* Struct that incapsulate the register map and data of the device */
typedef struct {
    /*  REGISTER MAP  */

    /*  Status Register            */
    uint8_t STR;
    /*  Lower Divisor Register     */
    uint8_t LDVR;
    /*  Lower Divisor Register     */
    uint8_t UDVR;
    /* Fifo Status Register        */
    uint8_t FSR;
    /*  Control Register           */
    uint8_t CTR;
    /*  Interrupt Status Register  */
    uint8_t ISR;
    /*  RX Register                */
    uint8_t RXR;
    /*  TX Register                */
    uint8_t TXR;

    /*  DEVICE DATA  */

    /* When the device interrupt in data stream mode because the rx fifo is full the stream retrieved is saved here */
    uint8_t *gDataStrmRxInt;

    /* When the device interrupt in normal mode because a byte is received that byte is saved here */
    uint8_t gDataRxInt;

    /* Set this bit if the device fails configuring */
    bool configFailed;
} volatile uart_t;

/* Used to refer to a paricular uart through a pointer */ 
uart_t *gHandle;



//------------------//
//  INITIALIZATION  //
//------------------//

/* The device is initialized with the standard configuration. */
void uart_initStd();

/* Initialize the device with baudrate and configuration parameters. */
void uart_init(uint32_t baudRate, uartDataWidth_t dataWidth, uartParityMode_t parityMode,uartStopBits_t stopBits, bool dataStreamMode, uint32_t threshold);



//-------------//
//  BAUD RATE  //
//-------------//

void uart_setBaudRate(uint32_t baudRate);   

uint32_t uart_getBaudRate();



//----------------//
//  RX OPERATION  //
//----------------//   

/* Receiver buffer empty status.*/
inline bool uart_rxEmpty();        

/* Retrieve a byte from the UART. */
const uint8_t uart_readByte(); 

/*
 *  Read a stream of bytes, return it as an array, the dimension of the stream is specified
 *  by the "size" parameter. The function use is legal to use only if the UART is in data 
 *  stream mode. Otherwise every read the UART will generate an interrupt request.
 */
const uint8_t* uart_readByteStream(size_t size);

/*  
 *  Read a string, the reading stops when the UART receives the '\0' character. The function 
 *  use is legal to use only if the UART is in data stream mode. Otherwise every read the UART 
 *  will generate an interrupt request.
 */
const char* uart_readString();  



//----------------//
//  TX OPERATION  //
//----------------//

/* Transmitter buffer full status.*/
inline bool uart_txFull();    

/* Transmit a byte */
void uart_sendByte(uint8_t data); 

/* 
 *  Transmit a stream of bytes, it is memorized in an array and the dimension of the stream is
 *  specified by the "size" parameter, if this is bigger than the buffer size, the function will
 *  become really slow because once the buffer is full, it needs to wait until the next character
 *  is sent.
 */
void uart_sendByteStream(const uint8_t *stream, size_t size);  

/* 
 *  Transmit a stream of character until the '\0' character is sended. if the string is bigger than  
 *  the buffer size, the function will become really slow because once the buffer is full, it needs 
 *  to wait until the next character.
 */
void uart_sendString(const char *string); 



//----------------------//
//  UART CONFIGURATION  //
//----------------------//

/* Get data width configuration parameter */
inline uint32_t uart_getDataWidth();   

/* Get parity mode configuration parameter */
inline uint32_t uart_getParityMode();  

/* Get stop bits number configuration parameter */
inline uint32_t uart_getStopBits();

/* Get data stream mode configuration */
inline bool uart_getDataStreamMode();

/* Set data width configuration parameter */
inline void uart_setDataWidth(uint32_t dataWidth);

/* Set parity mode configuration parameter */
inline void uart_setParityMode(uint32_t parityMode);

/* Set stop bits number configuration parameter */
inline void uart_setStopBits(uint32_t stopBitsNumber);  

/* Enable or disable data stream mode. */
inline void uart_setDataStreamMode(bool dataStreamMode);

/* Send the maximum number of data the rx fifo can store before interrupting */
inline void uart_setThresholdBuf(uint32_t threshold);



//---------------//
//  UART STATUS  //
//---------------//

/* Set standard configuration */
inline void uart_setStdConfig();

/* Acknowledge configuration request from another device, used in the interrupt service routine */
inline void uart_acknConfigReq();



//-------------//
//  INTERRUPT  //
//-------------//

/* Enable interrupt on overrun error */
inline void uart_enableIntOverrun(bool enable);     

/* Enable interrupt on parity error */
inline void uart_enableIntParity(bool enable); 

/* Enable interrupt on frame error */
inline void uart_enableIntFrame(bool enable);          

/* Enable interrupt on data received */
inline void uart_enableIntRxDRdy(bool enable);

/* Get interrupt ID */
inline uint32_t uart_getIntID();

/* This routine may not work because it's dependant on the system. */
void uart_interruptServiceRoutine() __attribute__((interrupt("IRQ")));


#endif