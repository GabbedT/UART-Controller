#ifndef UART_INCLUDED
#define UART_INCLUDED

#include <stdint.h>
#include <stdbool.h>
#include <stdlib.h>
#include "uart_driver.h"
#include "uart_regmap.h"

//------------------//
//  INITIALIZATION  //
//------------------//

void uart_initStd() {
    /* Set standard configuration bit */
    handle->CTR |= STD_CONFIG;
}

void uart_init(uint32_t baudRate, uartDataWidth_t dataWidth, uartParityMode_t parityMode,uartStopBits_t stopBits) {
    uart_setBaudRate(baudRate);

    /* Wait until the buffers are empty */
    while ((!uart_rxEmpty()) && (!uart_txEmpty())) { }

    /* Clear the configuration bit fields */
    uint32_t dataSTR = handle->STR;
    dataSTR &= ~(DATA_WIDTH | PARITY_MODE | STOP_BITS);

    /* Write parameters in the right register field */
    dataSTR |= dataWidth << 16;
    dataSTR |= parityMode << 18;
    dataSTR |= stopBits << 20;

    handle->STR = dataSTR;

    /* In this case the device will be the master, initiate a configuration process
     * by sending a configuration request. The device hardware will take care of the
     * devices intercommunication process. */
    uart_sendConfigReq();   
    uart_setDataStreamMode(false);
}   


//-------------//
//  BAUD RATE  //
//-------------//

void uart_setBaudRate(uint32_t baudRate) {
    /* Clear the divisor bit field */
    uint32_t dataCTR = handle->CTR;
    dataCTR &= ~(DIVISOR); 

    /* Calculate the divisor value to obtain the desired baud rate */
    dataCTR |= (uint16_t)((SYS_CLOCK_FREQ / (16 * baudRate)) - 1);
    handle->CTR = dataCTR;
}

uint32_t uart_getBaudRate() {
    uint16_t divisor = handle->CTR & DIVISOR;
    return SYS_CLOCK_FREQ / (16 * (divisor + 1));
}


//----------------//
//  RX OPERATION  //
//----------------//

bool uart_rxFull() {
    return handle->RXR & RX_FULL;
}

bool uart_rxEmpty() {
    return handle->RXR & RX_EMPTY;
}

const uint8_t uart_readByte() {
    return handle->RXR & DATA_RX;
}

const uint8_t* uart_readByteStream(size_t size) {
    /* Check if byte stream mode is enabled */
    if (!(handle->STR & DATA_STREAM_MODE)) {
        return NULL;
    } 

    /* Allocate the right amount of memory to store the data stream */
    uint8_t* byteStream = (uint8_t*) malloc(size * sizeof(uint8_t));

    /* Check if the allocation fails */
    if (byteStream == NULL) {
        return NULL;
    }

    /* Keep reading until the end of the array or there's no data in the fifo anymore */  
    while (uart_rxEmpty() || (byteStream < (byteStream + size))) {
        *byteStream = handle->RXR & DATA_RX;
        ++byteStream;    
    }

    return byteStream;
}

const char* UART_readString() {
    /* Check if byte stream mode is enabled */
    if (!(handle->STR & DATA_STREAM_MODE)) {
        return NULL;
    } 

    char* stringRx;

    /* Keep reading until the end of string ('\0') character is received
     * or the buffer is empty */
    do {
        /* Every cycle keep allocating new memory */
        stringRx = (char*) malloc(sizeof(char));

        /* Store character and increment the pointer */
        *stringRx = handle->RXR & DATA_RX;
        ++stringRx;    
    } while ((UART_RxEmpty()) || (*(stringRx - 1) == '\0'));

    return stringRx;
}


//----------------//
//  TX OPERATION  //
//----------------//

bool uart_txFull() {
    return handle->TXR & TX_FULL;
}

bool uart_txEmpty() {
    return handle->TXR & TX_EMPTY;
}

void uart_sendByte(uint8_t data) {
    /* Wait until TX FIFO is not full to not lose any data */
    while (uart_txFull()) { }

    /* Write the parameter in the tx data field */ 
    handle->TXR = (handle->TXR & ~(DATA_TX)) | data;
}

void uart_sendByteStream(const uint8_t *stream, size_t size) {
    /* Iterate until the last element of the array */
    while (stream < (stream + size)) {
        /* Wait until TX FIFO is not full to not lose any data */
        while (uart_txFull()) { }

        /* Write in the data tx field the function's parameter */
        handle->TXR = (handle->TXR & ~(DATA_TX)) | (*stream);
        ++stream;
    }
}

void uart_sendString(const char *string) {
    /* Iterate until the end of the string */
    while (*string != '\0') {
        /* Wait until TX FIFO is not full to not lose any data */
        while (uart_txFull()) { }

        /* Write in the data tx field the function's parameter */
        handle->TXR = (handle->TXR & ~(DATA_TX)) | ((uint8_t) *string);
        ++string;
    }
}


//----------------------//
//  UART CONFIGURATION  //
//----------------------//

uint32_t uart_getDataWidth() {
    return handle->STR & DATA_WIDTH;
}

uint32_t uart_getParityMode() {
    return handle->STR & PARITY_MODE;
}

uint32_t uart_getStopBits() {
    return handle->STR & STOP_BITS;
}

bool uart_getDataStreamMode() {
    return handle->STR & DATA_STREAM_MODE;
}

void uart_setDataWidth(uint32_t dataWidth) {
    handle->STR = (handle->STR & ~(DATA_WIDTH)) | (dataWidth << 16);
}

void uart_setParityMode(uint32_t parityMode) {
    handle->STR = (handle->STR & ~(PARITY_MODE)) | (parityMode << 18);
}

void uart_setStopBits(uint32_t stopBits) {
    handle->STR = (handle->STR & ~(STOP_BITS)) | (stopBits << 20);
}

void uart_setDataStreamMode(bool dataStreamMode) {
    handle->STR = (handle->STR & ~(DATA_STREAM_MODE)) | (dataStreamMode << 22);
}


//---------------//
//  UART STATUS  //
//---------------//

void uart_sendConfigReq() {
    handle->CTR |= CFG_REQ_MST;
}

void uart_setStdConfig() {
    handle->CTR |= STD_CONFIG;
}

void uart_acknConfigReq() {
    handle->CTR |= ACKN_CFG;
}


//-------------//
//  INTERRUPT  //
//-------------//

void uart_enableIntOverrun(bool enable) {
    handle->IMR = (handle->IMR & ~(INT_OVR_EN)) | enable;
}

void uart_enableIntParity(bool enable) {
    handle->IMR = (handle->IMR & ~(INT_PAR_EN)) | (enable << 1);
}

void uart_enableIntFrame(bool enable) {
    handle->IMR = (handle->IMR & ~(INT_FRM_EN)) | (enable << 2);
}

void uart_enableIntRxDRdy(bool enable) {
    handle->IMR = (handle->IMR & ~(INT_RXD_EN)) | (enable << 3);
}

uint32_t uart_getIntID() {
    return (handle->ISR & INT_ID) >> 1;
}


//---------------//
//  DEVICE INFO  //
//---------------//

uint32_t UART_getProductNumber() {
    return (handle->IFR & PRODUCT_NUMBER) >> 16;
}

uint32_t UART_getDeviceNumber() {
    return (handle->IFR & DEVICE_NUMBER) >> 24;
}

#endif