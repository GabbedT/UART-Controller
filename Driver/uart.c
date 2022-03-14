#ifndef UART_INCLUDED
#define UART_INCLUDED

#include <stdint.h>
#include <stdbool.h>
#include <stdlib.h>
#include "uart.h"
#include "uart_regmap.h"

//------------------//
//  INITIALIZATION  //
//------------------//

void uart_initStd() {
    /* Set standard configuration bit */
    gHandle->CTR |= STD_CONFIG;
}

void uart_init(uint32_t baudRate, uartDataWidth_t dataWidth, uartParityMode_t parityMode,uartStopBits_t stopBits, bool dataStreamMode, uint32_t threshold) {
    uart_setBaudRate(baudRate);
    uart_setDataStreamMode(dataStreamMode);
    uart_setThresholdBuf(threshold);

    /* Wait until the buffers are empty */
    while ((!uart_rxEmpty()) && (!uart_txEmpty())) { }

    /* Clear the configuration bit fields */
    uint32_t dataSTR = gHandle->STR;
    dataSTR &= ~(DATA_WIDTH | PARITY_MODE | STOP_BITS);

    /* Write parameters in the right register field */
    dataSTR |= dataWidth << 16;
    dataSTR |= parityMode << 18;
    dataSTR |= stopBits << 20;

    gHandle->STR = dataSTR;

    /* In this case the device will be the master, initiate a configuration process
     * by sending a configuration request. The device hardware will take care of the
     * devices intercommunication process.*/ 
    do { } while (!(gHandle->CTR & CFG_DONE));
}   


//-------------//
//  BAUD RATE  //
//-------------//

void uart_setBaudRate(uint32_t baudRate) {
    /* Clear the divisor bit field */
    uint32_t dataCTR = gHandle->CTR;
    dataCTR &= ~(DIVISOR); 

    /* Calculate the divisor value to obtain the desired baud rate */
    dataCTR |= (uint16_t)((SYS_CLOCK_FREQ / (16 * baudRate)) - 1);
    gHandle->CTR = dataCTR;
}

uint32_t uart_getBaudRate() {
    uint16_t divisor = gHandle->CTR & DIVISOR;
    return SYS_CLOCK_FREQ / (16 * (divisor + 1));
}


//----------------//
//  RX OPERATION  //
//----------------//

bool uart_rxFull() {
    return gHandle->RXR & RX_FULL;
}

bool uart_rxEmpty() {
    return gHandle->RXR & RX_EMPTY;
}

const uint8_t uart_readByte() {
    return gHandle->RXR & DATA_RX;
}

const uint8_t* uart_readByteStream(size_t size) {
    /* Check if byte stream mode is enabled */
    if (!(gHandle->STR & DATA_STREAM_MODE)) {
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
        *byteStream = gHandle->RXR & DATA_RX;
        ++byteStream;    
    }

    return byteStream;
}

const char* UART_readString() {
    /* Check if byte stream mode is enabled */
    if (!(gHandle->STR & DATA_STREAM_MODE)) {
        return NULL;
    } 

    char* stringRx;

    /* Keep reading until the end of string ('\0') character is received
     * or the buffer is empty */
    do {
        /* Every cycle keep allocating new memory */
        stringRx = (char*) malloc(sizeof(char));

        /* Store character and increment the pointer */
        *stringRx = gHandle->RXR & DATA_RX;
        ++stringRx;    
    } while ((UART_RxEmpty()) || (*(stringRx - 1) == '\0'));

    return stringRx;
}


//----------------//
//  TX OPERATION  //
//----------------//

bool uart_txFull() {
    return gHandle->TXR & TX_FULL;
}

bool uart_txEmpty() {
    return gHandle->TXR & TX_EMPTY;
}

void uart_sendByte(uint8_t data) {
    /* Wait until TX FIFO is not full to not lose any data */
    while (uart_txFull()) { }

    /* Write the parameter in the tx data field */ 
    gHandle->TXR = (gHandle->TXR & ~(DATA_TX)) | data;
}

void uart_sendByteStream(const uint8_t *stream, size_t size) {
    /* Iterate until the last element of the array */
    while (stream < (stream + size)) {
        /* Wait until TX FIFO is not full to not lose any data */
        while (uart_txFull()) { }

        /* Write in the data tx field the function's parameter */
        gHandle->TXR = (gHandle->TXR & ~(DATA_TX)) | (*stream);
        ++stream;
    }
}

void uart_sendString(const char *string) {
    /* Iterate until the end of the string */
    while (*string != '\0') {
        /* Wait until TX FIFO is not full to not lose any data */
        while (uart_txFull()) { }

        /* Write in the data tx field the function's parameter */
        gHandle->TXR = (gHandle->TXR & ~(DATA_TX)) | ((uint8_t) *string);
        ++string;
    }
}


//----------------------//
//  UART CONFIGURATION  //
//----------------------//

uint32_t uart_getDataWidth() {
    return (gHandle->STR & DATA_WIDTH) >> 16;
}

uint32_t uart_getParityMode() {
    return (gHandle->STR & PARITY_MODE) >> 18;
}

uint32_t uart_getStopBits() {
    return (gHandle->STR & STOP_BITS) >> 20;
}

bool uart_getDataStreamMode() {
    return (gHandle->STR & DATA_STREAM_MODE) >> 22;
}

uint32_t uart_getThresholdBuf() {
    return (gHandle->STR & FIFO_THRESHOLD) >> 23; 
}

void uart_setDataWidth(uint32_t dataWidth) {
    gHandle->STR = (gHandle->STR & ~(DATA_WIDTH)) | (dataWidth << 16);
}

void uart_setParityMode(uint32_t parityMode) {
    gHandle->STR = (gHandle->STR & ~(PARITY_MODE)) | (parityMode << 18);
}

void uart_setStopBits(uint32_t stopBits) {
    gHandle->STR = (gHandle->STR & ~(STOP_BITS)) | (stopBits << 20);
}

void uart_setDataStreamMode(bool dataStreamMode) {
    gHandle->STR = (gHandle->STR & ~(DATA_STREAM_MODE)) | (dataStreamMode << 22);
}

void uart_setThresholdBuf(uint32_t threshold) {
    if (threshold >= RX_FIFO_SIZE) {
        return;
    }
    gHandle->STR = (gHandle->STR & ~(FIFO_THRESHOLD)) | (threshold << 23);
}


//---------------//
//  UART STATUS  //
//---------------//

void uart_setStdConfig() {
    gHandle->CTR |= STD_CONFIG;
}

void uart_acknConfigReq() {
    gHandle->CTR |= ACKN_CFG;
}


//-------------//
//  INTERRUPT  //
//-------------//

void uart_enableIntOverrun(bool enable) {
    gHandle->IMR = (gHandle->IMR & ~(INT_OVR_EN)) | enable;
}

void uart_enableIntParity(bool enable) {
    gHandle->IMR = (gHandle->IMR & ~(INT_PAR_EN)) | (enable << 1);
}

void uart_enableIntFrame(bool enable) {
    gHandle->IMR = (gHandle->IMR & ~(INT_FRM_EN)) | (enable << 2);
}

void uart_enableIntRxDRdy(bool enable) {
    gHandle->IMR = (gHandle->IMR & ~(INT_RXD_EN)) | (enable << 3);
}

uint32_t uart_getIntID() {
    return (gHandle->ISR & INT_ID) >> 1;
}

/*
 *  Modify this routine if the processor needs to do some operations before accessing
 *  the device.
 */ 
void uart_interruptServiceRoutine() {
    uartInterruptID_t intID = (uartInterruptID_t) uart_getID();
    uint8_t trashValue;

    if (intID == INT_CONFIG_FAIL) {
        uint32_t baudRate = uart_getBaudRate();
        uint32_t dataWidth = uart_getDataWidth();
        uint32_t parityMode = uart_getParityMode();
        uint32_t stopBits = uart_getStopBits();
        uint32_t threshold = uart_getThresholdBuf();
        bool dataStreamMode = uart_getDataStreamMode();

        uart_init(baudRate, dataWidth, parityMode, stopBits, dataStreamMode, threshold);
        return;
    }

    if (intID == INT_OVERRUN) {
        trashValue = uart_readByte();
        return;
    }

    if (intID == INT_PARITY) {
        trashValue = uart_readByte();
        return;
    }

    if (intID == INT_CONFIG_REQ) {
        gHandle->CTR |= ACKN_CFG; 
        return;
    }

    if (intID == INT_RX_FULL) {
        if (uart_getDataStreamMode()) {
            *gDataStrmRxInt = uart_readByteStream(RX_FIFO_SIZE);
        } else {
            gDataRxInt = uart_readByte();
        }
        return;
    }

    if (intID == INT_RXD_RDY) {
        if (uart_getDataStreamMode()) {
            *gDataStrmRxInt = uart_readByteStream(uart_getThresholdBuf());
        } else {
            gDataRxInt = uart_readByte();
        }
        return;
    }
}


//---------------//
//  DEVICE INFO  //
//---------------//

uint32_t UART_getProductNumber() {
    return (gHandle->IFR & PRODUCT_NUMBER) >> 16;
}

uint32_t UART_getDeviceNumber() {
    return (gHandle->IFR & DEVICE_NUMBER) >> 24;
}

#endif