#include "uart_driver.h"

//----------------//
//  CONSTRUCTORS  //
//----------------//

UartCore::UartCore(uint32_t baseAddr, uint16_t baudRate, uint32_t dataWidth, uint32_t stopBits, uint32_t parityMode) {
    baseAddress = baseAddr;

    /* Wait until UART has no data to be transmitted */
    while (!UART_TxEmpty()) { }

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
    while (!UART_RxEmpty()) { }  
    UART_sendStopBitsNumberPacket(stopBits);
    while (!UART_RxEmpty()) { }
    UART_sendParityModePacket(parityMode);
    while (!UART_RxEmpty()) { }
    UART_sendEndConfigurationPacket();
    while (!UART_RxEmpty()) { }

    /* Check if there was any error */
    uint32_t error = UART_READ(baseAddress, ISR);
    if (error != 0) {
        /* Set standard configuration */ 
        uint32_t dataCFR = UART_READ(baseAddress, CFR) | CFR_SET_STD_CONFIG;
        UART_WRITE(baseAddress, CFR, dataCFR);
    }
}


UartCore::UartCore(uint32_t baseAddr) {
    baseAddress = baseAddr;

    /* Wait until UART has no data to be transmitted in the buffer */
    while (!UART_TxEmpty()) { }

    /* Set the correct baud rate to enable correct transmission of data */
    UART_setBaudRate((uint32_t) STD_BAUD_RATE);

    /* Set standard configuration */ 
    uint32_t dataCFR = UART_READ(baseAddress, CFR) | CFR_SET_STD_CONFIG;
    UART_WRITE(baseAddress, CFR, dataCFR);
}


//--------------------//
//  UART FIFO STATUS  //
//--------------------//

/*
 *  Since these functions are using the bool data type, we don't need to shift the value to the
 *  first bit position because if the data != 0 then it's true else it's false
 */

bool UartCore::UART_TxFull() {
    return UART_READ(baseAddress, TXR) & TXR_FIFO_TX_FULL;
}


bool UartCore::UART_TxEmpty() {
    return UART_READ(baseAddress, TXR) & TXR_FIFO_TX_EMPTY;
}


bool UartCore::UART_RxFull() {
    return UART_READ(baseAddress, RXR) & RXR_FIFO_RX_FULL;
}


bool UartCore::UART_RxEmpty() {
    return UART_READ(baseAddress, RXR) & RXR_FIFO_RX_EMPTY;
}


//------------------//
//  UART SEND DATA  //
//------------------//

void UartCore::UART_sendByte(uint8_t data) {
    /* Wait until TX FIFO is not full to not lose any data */
    while (UART_TxFull()) { }

    /* Write in the data tx field the function's parameter */
    uint32_t dataTXR = (UART_READ(baseAddress, TXR) & (~TXR_DATA_TX)) | data;
    UART_WRITE(baseAddress, TXR, dataTXR);
}


void UartCore::UART_sendByteStream(const uint8_t *stream, size_t size) {
    /* Iterate until the last element of the array */
    while (stream < (stream + size)) {
        /* Wait until TX FIFO is not full to not lose any data */
        while (UART_TxFull()) { }

        /* Write in the data tx field the function's parameter */
        uint32_t dataTXR = (UART_READ(baseAddress, TXR) & (~TXR_DATA_TX)) | (*stream);
        UART_WRITE(baseAddress, TXR, dataTXR);
        ++stream;
    }
}


void UartCore::UART_sendChar(char data) {
    /* Wait until TX FIFO is not full to not lose any data */
    while (UART_TxFull()) { }

    /* Write in the data tx field the function's parameter */
    uint32_t dataTXR = (UART_READ(baseAddress, TXR) & (~TXR_DATA_TX)) | ((uint8_t) data);
    UART_WRITE(baseAddress, TXR, dataTXR);
}


void UartCore::UART_sendString(const char *string) {
    /* Iterate until the end of the string */
    while ((uint8_t) *string != '\0') {
        /* Wait until TX FIFO is not full to not lose any data */
        while (UART_TxFull()) { }

        /* Write in the data tx field the function's parameter */
        uint32_t dataTXR = (UART_READ(baseAddress, TXR) & (~TXR_DATA_TX)) | ((uint8_t) *string);
        UART_WRITE(baseAddress, TXR, dataTXR);
        ++string;
    }
}


//------------------//
//  UART READ DATA  //
//------------------//

uint32_t UartCore::UART_readByte() {
    return UART_READ(baseAddress, TXR) & RXR_DATA_RX;
}


uint32_t* UartCore::UART_readByteStream(size_t size) {
    /* Allocate the right amount of memory to store the data stream */
    uint32_t* byteStream = (uint32_t*) malloc(size * sizeof(uint32_t));

    /* Keep reading until the end of the array or there's no data in the fifo anymore */  
    while ((UART_RxEmpty()) || (byteStream < (byteStream + size))) {
        *byteStream = UART_READ(baseAddress, RXR) & RXR_DATA_RX;
        ++byteStream;    
    }

    return byteStream;
}


char UartCore::UART_readChar() {
    return (char) (UART_READ(baseAddress, TXR) & RXR_DATA_RX);
}


char* UartCore::UART_readString() {
    char* stringReceived;

    /* Check if data stream mode is enabled */
    if (!(UART_READ(baseAddress, CFR) & CFR_DATA_STREAM_MODE)) {
        return;
    }

    /*
     *  Keep reading until the end of the array or there's no data in the fifo anymore 
     *  or the last received character is a end of string character 
     */
    do {
        /* Every cycle keep allocating new memory */
        stringReceived = (char*) malloc(sizeof(char));

        /* Store character and increment the pointer */
        *stringReceived = UART_READ(baseAddress, RXR) & RXR_DATA_RX;
        ++stringReceived;    
    } while ((UART_RxEmpty()) || (*(stringReceived - 1) == '\0'));

    return stringReceived;
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
    return UART_READ(baseAddress, CFR) & (~CFR_CONFIG_REQ_SLV);
}


void UartCore::UART_sendDataWidthPacket(uint32_t configCode) {
    /* Create configuration packet */
    uint8_t configPacket = (configCode << 2) & DATA_WIDTH_ID;

    /* Send the configuration packet */
    uint32_t dataTXR = (UART_READ(baseAddress, TXR) & (~TXR_DATA_TX)) | configPacket; 
    UART_WRITE(baseAddress, TXR, dataTXR);
}


void UartCore::UART_sendParityModePacket(uint32_t configCode) {
    /* Create configuration packet */
    uint8_t configPacket = (configCode << 2) & PARITY_MODE_ID;

    /* Send the configuration packet */
    uint32_t dataTXR = (UART_READ(baseAddress, TXR) & (~TXR_DATA_TX)) | configPacket; 
    UART_WRITE(baseAddress, TXR, dataTXR);
}


void UartCore::UART_sendStopBitsNumberPacket(uint32_t configCode) {
    /* Create configuration packet */
    uint8_t configPacket = (configCode << 2) & STOP_BITS_ID;

    /* Send the configuration packet */
    uint32_t dataTXR = (UART_READ(baseAddress, TXR) & (~TXR_DATA_TX)) | configPacket; 
    UART_WRITE(baseAddress, TXR, dataTXR);
}


void UartCore::UART_sendEndConfigurationPacket() {
    /* Create configuration packet */
    uint8_t configPacket = END_CONFIG_ID;

    /* Send the configuration packet */
    uint32_t dataTXR = (UART_READ(baseAddress, TXR) & (~TXR_DATA_TX)) | configPacket; 
    UART_WRITE(baseAddress, TXR, dataTXR);
}


//---------------//
//  GET METHODS  //
//---------------//

/*
 *  A get method will retrieve a specific bit field of a specific register and return it.
 */

uint32_t UartCore::getBaseAddress() {
    return baseAddress;
}


uint32_t UartCore::UART_getDataWidth() {
    return (UART_READ(baseAddress, CFR) & CFR_DATA_WIDTH) >> 16; 
}


uint32_t UartCore::UART_getParityMode() {
    return (UART_READ(baseAddress, CFR) & CFR_PARITY_MODE) >> 18; 
}


uint32_t UartCore::UART_getStopBitsNumber() {
    return (UART_READ(baseAddress, CFR) & CFR_STOP_BITS_NUM) >> 20; 
}


uint32_t UartCore::UART_getBaudRate() {
    uint16_t divisor = UART_READ(baseAddress, CFR) & CFR_DVSR;
    return SYS_CLOCK_FREQ / (16 * (divisor + 1));
}


uint32_t UartCore::UART_getInterruptCode() {
    return (UART_READ(baseAddress, ISR) & ISR_INT_ID) >> 1;
}


//---------------//
//  SET METHODS  //
//---------------//

/*
 *  A get method will generally retrieve the value of the corresponding register, reset the bit that needs
 *  to be written and write the value shifting it in the right position.
 */

void UartCore::UART_setIntOverrunError(bool enable) {
    uint32_t dataIMR = (UART_READ(baseAddress, IMR) & (~IMR_OVERRUN_ENABLE)) | ((uint32_t) enable);
    UART_WRITE(baseAddress, IMR, dataIMR);
}


void UartCore::UART_setIntParityError(bool enable) {
    uint32_t dataIMR = (UART_READ(baseAddress, IMR) & (~IMR_PARITY_ENABLE)) | ((uint32_t) enable << 1);
    UART_WRITE(baseAddress, IMR, dataIMR);
}


void UartCore::UART_setIntFrameError(bool enable) {
    uint32_t dataIMR = (UART_READ(baseAddress, IMR) & (~IMR_FRAME_ENABLE)) | ((uint32_t) enable << 2);
    UART_WRITE(baseAddress, IMR, dataIMR);
}


void UartCore::UART_setIntConfigError(bool enable) {
    uint32_t dataIMR = (UART_READ(baseAddress, IMR) & (~IMR_CONFIG_ENABLE)) | ((uint32_t) enable << 3);
    UART_WRITE(baseAddress, IMR, dataIMR);
}


void UartCore::UART_deassertConfigReqMst() {
    uint32_t dataCFR = (UART_READ(baseAddress, CFR) & (~CFR_CONFIG_REQ_MST));
    UART_WRITE(baseAddress, CFR, dataCFR);
}

void UartCore::UART_deassertConfigReqSlv() {
    uint32_t dataCFR = (UART_READ(baseAddress, CFR) & (~CFR_CONFIG_REQ_SLV));
    UART_WRITE(baseAddress, CFR, dataCFR);
}

void UartCore::UART_setDataStreamMode(bool dataStreamMode) {
    uint32_t dataCFR = ((UART_READ(baseAddress, CFR) & (~CFR_DATA_STREAM_MODE)) | ((uint32_t) dataStreamMode << 25));
    UART_WRITE(baseAddress, CFR, dataCFR);
}


//---------------//
//  DEVICE INFO  //
//---------------//

uint32_t UartCore::UART_getProductNumber() {
    return (UART_READ(baseAddress, IFR) & IFR_PROD_NUM) >> 16;
}

uint32_t UartCore::UART_getDeviceNumber() {
    return (UART_READ(baseAddress, IFR) & IFR_DEV_NUM) >> 23;
}