#ifndef UART_INCLUDED
#define UART_INCLUDED

#include <stdint.h>
#include <stdbool.h>
#include <stdlib.h>
#include "uart.h"
#include "uart_defines.h"

//------------------//
//  INITIALIZATION  //
//------------------//

void uart_std_config() {
    gHandle->device->CTR |= SET_STD_CONFIG;
}


void uart_init(uint32_t baudRate, uint8_t dataWidth, uint8_t parityMode, uint8_t stopBits, bool rxDataStreamMode, bool txDataStreamMode, uint8_t threshold) {
    uart_set_baud_rate(baudRate);
    uart_set_rxdsm(rxDataStreamMode);
    uart_set_txdsm(txDataStreamMode);
    uart_set_threshold(threshold);

    /* Store data until RX buffer is empty */  
    while (!(gHandle->device->FSR & RX_EMPTY)) {
        gHandle->rxDataBuf[gHandle->rxWrite_idx] = gHandle->device->RXR;
        ++gHandle->rxWrite_idx;
    }

    /* Clear the configuration bit fields */
    gHandle->config = gHandle->device->STR;
    gHandle->config &= ~(DATA_WIDTH | PARITY_MODE | STOP_BITS);

    /* Write parameters in the right register field */
    gHandle->config |= dataWidth | (parityMode << 2) | (stopBits << 4);
    gHandle->baudRate = baudRate;

    gHandle->device->STR = gHandle->config;

    /* Wait the device to start the configuration process */
    while (gHandle->device->CTR & CFG_DONE) {}
    /* Wait the device to end the configuration process */
    while (!(gHandle->device->CTR & CFG_DONE)) {}
}   



//-------------//
//  BAUD RATE  //
//-------------//

void uart_set_baudrate(uint32_t baudRate) {
    /* Calculate the divisor value to obtain the desired baud rate */
    uint16_t divisor = (uint16_t)((SYS_CLOCK_FREQ / (16 * baudRate)) - 1);
    gHandle->baudRate = baudRate;

    /* Setting the divisor in two different instruction is legal because
     * when the device receives a matching address with the first half 
     * of the register it waits until the other portion is addressed */
    gHandle->device->LDVR = (uint8_t) divisor;
    gHandle->device->UDVR = (uint8_t) ((divisor & 0xFF00) >> 8);
}



//----------------//
//  RX OPERATION  //
//----------------//


uint8_t uart_read_data() {
    return gHandle->device->RXR;
}


void uart_read_data_stream(uint8_t* stream, size_t size) {
    /* Check if byte stream mode is enabled or RX fifo is empty */
    if (!(gHandle->device->STR & RX_DATA_STREAM_MODE) || (gHandle->device->FSR & RX_EMPTY)) {
        return NULL;
    } 

    /* Keep reading until the end of the array or there's no data in the fifo anymore */  
    for (size_t i = 0; i < size; ++i) {
        stream[i] = gHandle->device->RXR;
    }
}


void uart_read_string(char* str) {
    /* Check if byte stream mode is enabled */
    if (!(gHandle->device->STR & RX_DATA_STREAM_MODE)) {
        return NULL;
    } 

    size_t i = 0;

    /* Keep reading until the end of string ('\0') character is received */
    do {
        str[i] = gHandle->device->RXR;
    } while (str[i] != '\0');
}


void uart_read_stream_rxbuf(uint8_t* stream, size_t size) {
    for (int i = 0; i < size; ++i) {
        /* Check if the buffer is not empty */
        if (gHandle->rxRead_idx < gHandle->rxWrite_idx) {
            stream[i] = gHandle->rxDataBuf[gHandle->rxRead_idx];
            ++gHandle->rxRead_idx;
        } else {
            gHandle->rxRead_idx = 0;
            gHandle->rxWrite_idx = 0;
        }
    }
}


uint8_t uart_read_data_rxbuf() {
    uint8_t data;

    /* Check if the buffer is not empty */
    if (gHandle->rxRead_idx < gHandle->rxWrite_idx) {
        data = gHandle->rxDataBuf[gHandle->rxRead_idx];
        ++gHandle->rxRead_idx;

        /* If buffer become empty reset indexes */
        if (gHandle->rxRead_idx == gHandle->rxWrite_idx) {
            gHandle->rxRead_idx = 0;
            gHandle->rxWrite_idx = 0;
        }
    } 

    return data;
}



//----------------//
//  TX OPERATION  //
//----------------//


void uart_send_data(const uint8_t data) {
    /* Wait until TX FIFO is not full to not lose any data */
    while (gHandle->device->FSR & TX_FULL) { }

    /* Write the parameter in the tx data field */ 
    gHandle->device->TXR = data;
}


void uart_send_data_stream(const uint8_t *stream, size_t size) {
    /* Iterate until the last element of the array */
    for (int i = 0; i < size; ++i) {
        /* Wait until TX FIFO is not full to not lose any data */
        while (gHandle->device->FSR & TX_FULL) { }

        /* Write in the data tx field the function's parameter */
        gHandle->device->TXR = stream[i];
    }
}


void uart_send_string(const char *string) {
    size_t i = 0;

    /* Iterate until the end of the string */
    while (string[i] != '\0') {
        /* Wait until TX FIFO is not full to not lose any data */
        while (gHandle->device->FSR & TX_FULL) { }

        /* Write in the data tx field the function's parameter */
        gHandle->device->TXR = (uint8_t) string[i];
    }
}


void uart_fill_stream_txbuf(const uint8_t *stream, const size_t size) {
    for (int i = 0; i < size; ++i) {
        if (gHandle->txWrite_idx < TX_UART_BUFFER_SIZE) {
            gHandle->txDataBuf[gHandle->txWrite_idx] = stream[i];
            ++gHandle->txWrite_idx;
        } else {
            return;
        }
    }
}


void uart_fill_data_txbuf(const uint8_t data) {
    if (gHandle->txWrite_idx < TX_UART_BUFFER_SIZE) {
        gHandle->txDataBuf[gHandle->txWrite_idx] = data;
        ++gHandle->txWrite_idx;
    } else {
        return;
    }    
}



//----------------------//
//  UART CONFIGURATION  //
//----------------------//

void uart_set_configuration(uint8_t dataWidth, uint8_t parityMode, uint8_t stopBits) {
    uint8_t dataSTR = gHandle->device->STR & (~(STOP_BITS | PARITY_MODE | DATA_WIDTH));
    dataSTR = ((stopBits << 4) | (parityMode << 2) | dataWidth);

    /* Write configuration */
    gHandle->device->STR = dataSTR;
}


void uart_set_rxdsm(bool dataStreamMode) {
    gHandle->device->STR = (gHandle->device->STR & ~(RX_DATA_STREAM_MODE)) | (dataStreamMode << 6);
}

void uart_set_txdsm(bool dataStreamMode) {
    gHandle->device->STR = (gHandle->device->STR & ~(TX_DATA_STREAM_MODE)) | (dataStreamMode << 7);
}


void uart_set_threshold(uint32_t threshold) {
    if (threshold >= RX_FIFO_SIZE) {
        return;
    }
    gHandle->device->STR = (gHandle->device->STR & ~(FIFO_THRESHOLD)) | threshold;
}


void uart_set_communication_mode(uint8_t mode){
    gHandle->device->STR = (gHandle->device->STR & ~(COMM_MODE)) | (mode << 4);
}


void uart_enable_config_req(bool enableReq) {
    gHandle->device->STR = (gHandle->device->STR & ~(EN_CFG_REQ)) | (enableReq << 3);
}



//-------------//
//  INTERRUPT  //
//-------------//

void uart_enable_int_overrun(bool enable) {
    gHandle->device->ISR = (gHandle->device->ISR & ~(INT_OVR_EN)) | (enable << 3);
}


void uart_enable_int_parity(bool enable) {
    gHandle->device->ISR = (gHandle->device->ISR & ~(INT_PAR_EN)) | (enable << 4);
}


void uart_enable_int_frame(bool enable) {
    gHandle->device->ISR = (gHandle->device->ISR & ~(INT_FRM_EN)) | (enable << 5);
}


void uart_enable_int_rxrdy(bool enable) {
    gHandle->device->ISR = (gHandle->device->ISR & ~(INT_RX_RDY_EN)) | (enable << 6);
}

void uart_enable_int_txrdy(bool enable) {
    gHandle->device->ISR = (gHandle->device->ISR & ~(INT_TX_RDY_EN)) | (enable << 7);
}


/*
 *  Modify this routine if the processor needs to do some operations before accessing
 *  the device.
 */ 
void uart_interruptServiceRoutine() {
    uint8_t intID = gHandle->device->ISR & INT_ID;
    uint8_t trashValue;

    switch (intID) {
        case INT_TX_DONE:
            /* If the buffer is not empty */
            if (gHandle->txWrite_idx != 0) {
                if (gHandle->device->STR & TX_DATA_STREAM_MODE) {
                    /* Send a stream of bytes and reset the indexes */
                    uart_send_data_stream(gHandle->txDataBuf, gHandle->txWrite_idx);
                    gHandle->txWrite_idx = 0;
                    gHandle->txRead_idx = 0;
                } else {
                    /* Send one character */
                    uart_send_data(gHandle->txDataBuf[gHandle->txRead_idx]);
                    ++gHandle->txRead_idx;

                    /* If all the data in the buffer has been sent reset the pointers */
                    if (gHandle->txRead_idx == gHandle->txWrite_idx) {
                        gHandle->txWrite_idx = 0;
                        gHandle->txRead_idx = 0;
                    }
                }
            }
        break;

        case INT_CONFIG_FAIL:
            /* Update data */
            gHandle->failedConfig = true;
        break;

        case INT_OVERRUN:
            /* Update data */
            ++gHandle->errors;
            trashValue = uart_read_data();
        break;

        case INT_PARITY:
            /* Update data */
            ++gHandle->errors;
            trashValue = uart_read_data();
        break;

        case INT_FRAME:
            /* Update data */
            ++gHandle->errors;
            trashValue = uart_read_data();
        break;

        case INT_RXD_RDY:
            if (gHandle->device->STR & RX_DATA_STREAM_MODE) {
                /* The cycle runs until the RX fifo is empty */
                while (!(gHandle->device->FSR & RX_EMPTY)) {
                    /* If the buffer is not full */
                    if (gHandle->rxWrite_idx < RX_UART_BUFFER_SIZE) {
                        /* Write buffer and update index */
                        gHandle->rxDataBuf[gHandle->rxWrite_idx] = uart_read_data();
                        ++gHandle->rxWrite_idx;
                    } else {
                        break;
                    }
                }
            } else {
                if (gHandle->rxWrite_idx < RX_UART_BUFFER_SIZE) {
                    /* Write buffer and update index */
                    gHandle->rxDataBuf[gHandle->rxWrite_idx] = uart_read_data();
                    ++gHandle->rxWrite_idx;
                } else {
                    break;
                } 
            }
        break;

        case INT_RX_FULL:
            if (gHandle->device->STR & RX_DATA_STREAM_MODE) {
                /* The cycle runs until the RX fifo is empty */
                while (!(gHandle->device->FSR & RX_EMPTY)) {
                    /* If the buffer is not full */
                    if (gHandle->rxWrite_idx < RX_UART_BUFFER_SIZE) {
                        /* Write buffer and update index */
                        gHandle->rxDataBuf[gHandle->rxWrite_idx] = uart_read_data();
                        ++gHandle->rxWrite_idx;
                    } else {
                        break;
                    }
                }
            } else {
                if (gHandle->rxWrite_idx < RX_UART_BUFFER_SIZE) {
                    /* Write buffer and update index */
                    gHandle->rxDataBuf[gHandle->rxWrite_idx] = uart_read_data();
                    ++gHandle->rxWrite_idx;
                } else {
                    break;
                } 
            }
        break;

        case INT_CONFIG_REQ:
            /* Acknowledge request */
            gHandle->device->CTR |= ACK_REQ;
        break;
        
        default: break;
    }
}


#endif