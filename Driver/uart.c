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

void uart_setStdConfig() {
    gHandle->CTR |= STD_CONFIG;
    uart_setBaudRate(9600);
    uart_setDataStreamMode(false);
    uart_setThresholdBuf(0);
}


void uart_acknConfigReq() {
    gHandle->CTR |= ACKN_CFG;
}


void uart_initStd() {
    /* Set standard configuration bit */
    uart_setStdConfig();
}

void uart_init(uint32_t baudRate, uartDataWidth_t dataWidth, uartParityMode_t parityMode,uartStopBits_t stopBits, bool dataStreamMode, uint32_t threshold) {
    uart_setBaudRate(baudRate);
    uart_setDataStreamMode(1);
    uart_setThresholdBuf(threshold);
    uint8_t trashData;

    /* Wait until the buffers are empty */  
    while ((!uart_rxEmpty()) && (!uart_txEmpty())) {
        trashData = gHandle->RXR;
    }
    uart_setDataStreamMode(dataStreamMode);

    /* Clear the configuration bit fields */
    uint8_t dataSTR = gHandle->STR;
    dataSTR &= ~(DATA_WIDTH | PARITY_MODE | STOP_BITS);

    /* Write parameters in the right register field */
    dataSTR |= dataWidth;
    dataSTR |= parityMode << 2;
    dataSTR |= stopBits << 4;

    gHandle->STR = dataSTR;

    /* Send 3 SYN character */
    for (int i = 0; i < 3; i++) {
        uart_sendByte(0x16);
    }

    /* In this case the device will be the master, initiate a configuration process
     * by sending a configuration request. The device hardware will take care of the
     * devices intercommunication process.*/ 
    gHandle->CTR |= CFG_REQ_MST;
    do { } while (!(gHandle->CTR & CFG_DONE));

    /* Send another SYN character to reset the internal counters of the slave */
    uart_sendByte(0x16);
}   


//-------------//
//  BAUD RATE  //
//-------------//

void uart_setBaudRate(uint32_t baudRate) {
    /* Calculate the divisor value to obtain the desired baud rate */
    uint16_t divisor = (uint16_t)((SYS_CLOCK_FREQ / (16 * baudRate)) - 1);

    /* Setting the divisor in two different instruction is legal because
     * when the device receives a matching address with the first half 
     * of the register it waits until the other portion is addressed */
    gHandle->LDVR = (uint8_t) divisor;
    gHandle->UDVR = (uint8_t) ((divisor & 0xFF00) >> 8);
}

uint32_t uart_getBaudRate() {
    uint16_t divisor = ((gHandle->CTR & UPPER_DIVISOR) << 8) | (gHandle->CTR & LOWER_DIVISOR);
    return SYS_CLOCK_FREQ / (16 * (divisor + 1));
}


//----------------//
//  RX OPERATION  //
//----------------//


bool uart_rxEmpty() {
    return gHandle->FSR & RX_EMPTY;
}


const uint8_t uart_readByte() {
    return gHandle->RXR;
}


const uint8_t* uart_readByteStream(size_t size) {
    /* Check if byte stream mode is enabled */
    if (!(gHandle->STR & RX_DATA_STREAM_MODE)) {
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
        *byteStream = gHandle->RXR;
        ++byteStream;    
    }

    return byteStream;
}


const char* uart_readString() {
    /* Check if byte stream mode is enabled */
    if (!(gHandle->STR & RX_DATA_STREAM_MODE)) {
        return NULL;
    } 

    char* stringRx;

    /* Keep reading until the end of string ('\0') character is received
     * or the buffer is empty */
    do {
        /* Every cycle keep allocating new memory */
        stringRx = (char*) malloc(sizeof(char));

        /* Store character and increment the pointer */
        *stringRx = gHandle->RXR;
        ++stringRx;    
    } while ((uart_RxEmpty()) || (*(stringRx - 1) == '\0'));

    return stringRx;
}



//----------------//
//  TX OPERATION  //
//----------------//

bool uart_txFull() {
    return gHandle->FSR & TX_FULL;
}


void uart_sendByte(uint8_t data) {
    /* Wait until TX FIFO is not full to not lose any data */
    while (uart_txFull()) { }

    /* Write the parameter in the tx data field */ 
    gHandle->TXR = data;
}


void uart_sendByteStream(const uint8_t *stream, size_t size) {
    /* Iterate until the last element of the array */
    while (stream < (stream + size)) {
        /* Wait until TX FIFO is not full to not lose any data */
        while (uart_txFull()) { }

        /* Write in the data tx field the function's parameter */
        gHandle->TXR = *stream;
        ++stream;
    }
}


void uart_sendString(const char *string) {
    /* Iterate until the end of the string */
    while (*string != '\0') {
        /* Wait until TX FIFO is not full to not lose any data */
        while (uart_txFull()) { }

        /* Write in the data tx field the function's parameter */
        gHandle->TXR = (uint8_t) *string;
        ++string;
    }
}



//----------------------//
//  UART CONFIGURATION  //
//----------------------//

uint32_t uart_getDataWidth() {
    return (gHandle->STR & DATA_WIDTH);
}


uint32_t uart_getParityMode() {
    return (gHandle->STR & PARITY_MODE) >> 2;
}


uint32_t uart_getStopBits() {
    return (gHandle->STR & STOP_BITS) >> 4;
}


bool uart_getRxDataStreamMode() {
    return (gHandle->STR & RX_DATA_STREAM_MODE) >> 6;
}

bool uart_getTxDataStreamMode() {
    return (gHandle->STR & TX_DATA_STREAM_MODE) >> 6;
}


uint32_t uart_getThresholdBuf() {
    return (gHandle->FSR & FIFO_THRESHOLD); 
}


void uart_setDataWidth(uint32_t dataWidth) {
    gHandle->STR = (gHandle->STR & ~(DATA_WIDTH)) | (dataWidth);
}


void uart_setParityMode(uint32_t parityMode) {
    gHandle->STR = (gHandle->STR & ~(PARITY_MODE)) | (parityMode << 2);
}


void uart_setStopBits(uint32_t stopBits) {
    gHandle->STR = (gHandle->STR & ~(STOP_BITS)) | (stopBits << 4);
}


void uart_setRxDataStreamMode(bool dataStreamMode) {
    gHandle->STR = (gHandle->STR & ~(RX_DATA_STREAM_MODE)) | (dataStreamMode << 6);
}

void uart_setTxDataStreamMode(bool dataStreamMode) {
    gHandle->STR = (gHandle->STR & ~(TX_DATA_STREAM_MODE)) | (dataStreamMode << 6);
}


void uart_setThresholdBuf(uint32_t threshold) {
    if ((threshold >= RX_FIFO_SIZE) || (threshold == 0)) {
        return;
    }
    gHandle->STR = (gHandle->STR & ~(FIFO_THRESHOLD)) | threshold;
}



//-------------//
//  INTERRUPT  //
//-------------//

void uart_enableIntOverrun(bool enable) {
    gHandle->ISR = (gHandle->ISR & ~(INT_OVR_EN)) | (enable << 4);
}


void uart_enableIntParity(bool enable) {
    gHandle->ISR = (gHandle->ISR & ~(INT_PAR_EN)) | (enable << 5);
}


void uart_enableIntFrame(bool enable) {
    gHandle->ISR = (gHandle->ISR & ~(INT_FRM_EN)) | (enable << 6);
}


void uart_enableIntRxDRdy(bool enable) {
    gHandle->ISR = (gHandle->ISR & ~(INT_RXD_EN)) | (enable << 7);
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

    if (intID == INT_TX_DONE) {
        gHandle->ISR |= INT_ACKN;
        return;
    }else if (intID == INT_CONFIG_FAIL) {
        gHandle->configFailed = true;
        return;
    } else if (intID == INT_OVERRUN) {
        trashValue = uart_readByte();
        return;
    } else if (intID == INT_PARITY) {
        trashValue = uart_readByte();
        return;
    } else if (intID == INT_CONFIG_REQ) {
        gHandle->CTR |= ACKN_CFG; 
        return;
    } else if (intID == INT_RX_FULL) {
        if (uart_getDataStreamMode()) {
            gHandle->gDataStrmRxInt = uart_readByteStream(RX_FIFO_SIZE);
        } else {
            gHandle->gDataRxInt = uart_readByte();
        }
        return;
    } else if (intID == INT_RXD_RDY) {
        if (uart_getDataStreamMode()) {
            gHandle->gDataStrmRxInt = uart_readByteStream(uart_getThresholdBuf());
        } else {
            gHandle->gDataRxInt = uart_readByte();
        }
        return;
    }
}


#endif