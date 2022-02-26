#include "uart_driver.h"

//----------------//
//  CONSTRUCTORS  //
//----------------//

UartCore::UartCore(uint32_t baseAddr, uint16_t baudRate, uint32_t dataWidth, uint32_t stopBits, uint32_t parityMode) {
    baseAddress = baseAddr;

    /* Wait until UART has no data to be transmitted in the buffer */
    while (!UART_TxEmpty) { }

    /* Set the correct baud rate to enable correct transmission of data */
    UART_setBaudRate(baudRate);

    /* Clean the RX FIFO */
    uint32_t trashValue;
    while (!UART_RxEmpty()) {
        trashValue = UART_READ(baseAddress, RXR);
    }

    /* Send a configuration request signal to initialize the configuration process */
    UART_sendConfigReq();

    /* Send configuration packet, then wait the acknowledge packet before sending other transactions */
    UART_sendDataWidthPacket(dataWidth);
    while (UART_RxEmpty()) { }  
    UART_sendStopBitsNumberPacket(stopBits);
    while (UART_RxEmpty()) { }
    UART_sendParityModePacket(parityMode);
    while (UART_RxEmpty()) { }
    UART_sendEndConfigurationPacket();
    while (UART_RxEmpty()) { }

    /* Check if there was any error */
    uint32_t error = UART_READ(baseAddress, ISR);
    if (error != 0) {
        /* Set standard configuration */ 
        uint32_t dataCFG = UART_READ(baseAddress, CFR) | CFG_SET_STD_CONFIG;
        UART_WRITE(baseAddress, CFR, dataCFG);
    }
}


UartCore::UartCore(uint32_t baseAddr) {
    baseAddress = baseAddr;

    /* Wait until UART has no data to be transmitted in the buffer */
    while (!UART_TxEmpty) { }

    /* Set the correct baud rate to enable correct transmission of data */
    UART_setBaudRate((uint32_t) STD_BAUD_RATE);

    /* Set standard configuration */ 
    uint32_t dataCFG = UART_READ(baseAddress, CFR) | CFG_SET_STD_CONFIG;
    UART_WRITE(baseAddress, CFR, dataCFG);
}


//-----------------//
//  SET BAUD RATE  //
//-----------------//

void UartCore::UART_setBaudRate(uint32_t baudRate) {
    /* Calculate the divisor value to obtain the desired baud rate */
    uint16_t divisor = (SYS_CLOCK_FREQ / (16 * baudRate)) - 1;

    /* Clean the divisor bitfield and write a new value */
    uint32_t dataCFR = (UART_READ(baseAddress, CFR) & 0xFFFF0000) | divisor; 
    UART_WRITE(baseAddress, CFR, dataCFR);
}


//-----------------//
//  CONFIGURATION  //
//-----------------//

void UartCore::UART_sendConfigReq() {
    /* Set the configuration request bit to one */
    uint32_t dataCFR = UART_READ(baseAddress, CFR) | CFR_CONFIG_REQ_MST;
    UART_WRITE(baseAddress, CFR, dataCFR);
}

bool UartCore::UART_checkConfigReq() {
    return UART_READ(baseAddress, CFR) & !CFG_CONFIG_REQ_SLV;
}


void UartCore::UART_sendDataWidthPacket(uint32_t configCode) {
    /* Create configuration packet */
    uint8_t configPacket = (configCode << 2) & DATA_WIDTH_ID;

    /* Send the configuration packet */
    uint32_t dataTXR = UART_READ(baseAddress, TXR) | configPacket; 
    UART_WRITE(baseAddress, TXR, dataTXR);
}


void UartCore::UART_sendParityModePacket(uint32_t configCode) {
    /* Create configuration packet */
    uint8_t configPacket = (configCode << 2) & PARITY_MODE_ID;

    /* Send the configuration packet */
    uint32_t dataTXR = UART_READ(baseAddress, TXR) | configPacket; 
    UART_WRITE(baseAddress, TXR, dataTXR);
}


void UartCore::UART_sendStopBitsNumberPacket(uint32_t configCode) {
    /* Create configuration packet */
    uint8_t configPacket = (configCode << 2) & STOP_BITS_ID;

    /* Send the configuration packet */
    uint32_t dataTXR = UART_READ(baseAddress, TXR) | configCode; 
    UART_WRITE(baseAddress, TXR, dataTXR);
}


void UartCore::UART_sendEndConfigurationPacket() {
    /* Create configuration packet */
    uint8_t configPacket = END_CONFIG_ID;

    /* Send the configuration packet */
    uint32_t dataTXR = UART_READ(baseAddress, TXR) | configPacket; 
    UART_WRITE(baseAddress, TXR, dataTXR);
}

