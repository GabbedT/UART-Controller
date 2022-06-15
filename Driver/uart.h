#ifndef UART_HEADER_INCLUDED
#define UART_HEADER_INCLUDED

#include <stdint.h>
#include <stdbool.h>
#include <stdlib.h>
#include "uart_defines.h"


//----------//
//  DEVICE  //
//----------//

typedef struct {

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

} volatile uart_registers_t;


/* Struct that incapsulate the register map and data of the device */
typedef struct {

    /* Pointer to a device to support MMIO */
    uart_registers_t *device;

    /* Device configuration */
    uint8_t config;
    bool failedConfig;
    uint32_t baudRate;
    uint32_t errors;

    /* The buffer is automatically loaded when new data is 
     * ready if interrupts are enabled. (RX BUFFER != RX FIFO) */
    uint8_t rxDataBuf[RX_UART_BUFFER_SIZE];
    size_t rxWrite_idx;
    size_t rxRead_idx;

    /* The buffer automatically load new data into the device
     * every time it interrupts. (TX BUFFER != TX FIFO) */
    uint8_t txDataBuf[TX_UART_BUFFER_SIZE];
    size_t txWrite_idx;
    size_t txRead_idx;

} volatile uart_t;


/* Used to refer to a paricular uart through a pointer */ 
uart_t *gHandle;



//------------------//
//  INITIALIZATION  //
//------------------//

/* The device is initialized with the standard configuration. */
void uart_std_config();


/* Initialize the device with baudrate and configuration parameters. */
void uart_init(uint32_t baudRate, uint8_t dataWidth, uint8_t parityMode, uint8_t stopBits, bool rxDataStreamMode, bool txDataStreamMode, uint8_t threshold);



//-------------//
//  BAUD RATE  //
//-------------//

void uart_set_baudrate(uint32_t baudRate);   



//----------------//
//  RX OPERATION  //
//----------------//         

/* Retrieve a byte from the UART. */
uint8_t uart_read_data(); 


/*
 *  Read a stream of bytes, return it as an array, the dimension of the stream is specified
 *  by the "size" parameter. The function use is legal to use only if the UART is in data 
 *  stream mode. Otherwise every read the UART will generate an interrupt request.
 */
void uart_read_data_stream(uint8_t* stream, size_t size);


/*  
 *  Read a string, the reading stops when the UART receives the '\0' character. The function 
 *  use is legal to use only if the UART is in data stream mode. Otherwise every read the UART 
 *  will generate an interrupt request.
 */
void uart_read_string(char* str);  


/* 
 *  Read a stream of data from the receiver buffer, to empty the buffer use the write pointer
 *  'rxWrite_idx' as size parameter.
 */
void uart_read_stream_rxbuf(uint8_t* stream, size_t size);


/* 
 *  Read a single byte of data from the receiver buffer
 */
uint8_t uart_read_data_rxbuf();



//----------------//
//  TX OPERATION  //
//----------------//  


/* Transmit a byte */
void uart_send_data(const uint8_t data); 


/* 
 *  Transmit a stream of bytes, it is memorized in an array and the dimension of the stream is
 *  specified by the "size" parameter, if this is bigger than the buffer size, the function will
 *  become really slow because once the buffer is full, it needs to wait until the next character
 *  is sent.
 */
void uart_send_data_stream(const uint8_t *stream, const size_t size);  


/* 
 *  Transmit a stream of character until the '\0' character is sended. if the string is bigger than  
 *  the buffer size, the function will become really slow because once the buffer is full, it needs 
 *  to wait until the next character.
 */
void uart_send_string(const char *string); 


/*
 *  Fill the transmitter buffer with a stream of data ready to be sent.
 */
void uart_fill_stream_txbuf(const uint8_t *stream, const size_t size);

/*
 *  Fill the transmitter buffer with a single byte of data ready to be sent.
 */
void uart_fill_data_txbuf(const uint8_t data);



//----------------------//
//  UART CONFIGURATION  //
//----------------------//

void uart_set_configuration(uint8_t dataWidth, uint8_t parityMode, uint8_t stopBits);

/* Enable or disable receiver data stream mode. */
void uart_set_rxdsm(bool dataStreamMode);


/* Enable or disable transmitter data stream mode. */
void uart_set_txdsm(bool dataStreamMode);


/* Send the maximum number of data the rx fifo can store before interrupting */
void uart_set_threshold(uint32_t threshold);


/* Set communication mode */
void uart_set_communication_mode(uint8_t mode); 


/* Enable receiving configuration request */
void uart_enable_config_req(bool enableReq);



//-------------//
//  INTERRUPT  //
//-------------//

/* Enable interrupt on overrun error */
void uart_enable_int_overrun(bool enable);     


/* Enable interrupt on parity error */
void uart_enable_int_parity(bool enable); 


/* Enable interrupt on frame error */
void uart_enable_int_frame(bool enable);          


/* Enable interrupt on data received */
void uart_enable_int_rxrdy(bool enable);

/* Enable interrupt on data transmitted */
void uart_enable_int_txrdy(bool enable);


/* This routine may not work because it's dependant on the system. */
void uart_interrupt_service_routine() __attribute__((interrupt("IRQ")));


#endif