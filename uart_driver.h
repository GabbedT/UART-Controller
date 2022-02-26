#ifndef UART_CORE_INCLUDED
#define UART_CORE_INCLUDED

#include <stdint.h>
#include <stdbool.h>
#include <stdlib.h>

/*
 *  It's important to define the system clock here or include it (in this case comment the definition).
 *  The system clock is used to calculate the desired baud rate.
 */
#define SYS_CLOCK_FREQ 100'000'000  /*  100MHz clock  */


/*
 *  Return a specific register address, it is mandatory to use as offset a value between 0 and 5 (see register map definition)
 */
#define REG_ADDRESS(baseAddr, offset)  ( baseAddr + (4 * offset) ) 


/* 
 *  Read from a specific register of the UART. The base address is the address of the UART device in memory, 
 *  the offset is the address of the specific register.
 */
#define UART_READ(baseAddr, offset)  ( *(volatile uint32_t *) REG_ADDRESS(baseAddr, offset) )


/*
 *  Write a specific register in the UART. Since registers are 32 bits, dataWrite is converted as a 32 bit 
 *  unsigned int.
 */
#define UART_WRITE(baseAddr, offset, dataWrite)  ( *(volatile uint32_t *) REG_ADDRESS(baseAddr, offset) = (uint32_t) dataWrite )


/*  
 *  The packets sent to the other device to configure it are recognized by their ID, the configuration code
 *  is then used to select an option for that determined configuration 
 */
#define END_CONFIG_ID 0b00      /*  Packet to end a configuration process  */
#define DATA_WIDTH_ID 0b01      /*  Packet to configure the data width  */
#define STOP_BITS_ID 0b10       /*  Packet to configure the number of stop bits  */
#define PARITY_MODE_ID 0b11     /*  Packet to configure the parity mode  */


/*  
 *  Standard configuration:
 *  8 Data bits
 *  1 Stop bit
 *  No parity
 *  9600 Baud rate
 */
#define STD_DATA_WIDTH  0b11
#define STD_STOP_BITS  0b00
#define STD_PARITY_MODE  0b00
#define STD_BAUD_RATE 9600


/* 
 *  Register map definition 
 */
#define CFR 0       /*  Configuration Register  */
#define ISR 1       /*  Interrupt Status Register  */
#define IMR 2       /*  Interrupt Mask Register  */
#define RXR 3       /*  RX Register  */
#define TXR 4       /*  TX Register  */
#define IDR 5       /*  ID Register  */


class UartCore {

    /*
     *  Masks for bit extraction, registers are 32 bits so the mask is 8 digit in hexadecimal.
     *  Some bit fields are not defined, that means that those are reserved and must not be 
     *  accessed for any reason.
     */
    enum {

        /* 
         *  CFR Register bit fields 
         *  ------------------------------------------------------------------------
         *  Bits    | Description                                   | Access mode |
         *  ------------------------------------------------------------------------
         *  [15:0]  | Divisor value to obtain the desired baud rate | R / W       |
         *  [17:16] | Data width configuration ID                   | R / W       |
         *  [19:18] | Parity configuration ID                       | R / W       | 
         *  [21:20] | Stop bits number configuration ID             | R / W       | 
         *  [22]    | Configuration request                         | W           | 
         *  [23]    | Configuration requested                       | R           |
         *  [24]    | Set standard configuration                    | W           |
         *  [31:25] | Reserved                                      | NONE        |
         * -------------------------------------------------------------------------
         */
        
        CFR_DVSR = 0x0000FFFF,
        CFR_DATA_WIDTH = 0x00030000,
        CFR_PARITY_MODE = 0x000C0000,
        CFR_STOP_BITS_NUM = 0x00300000,
        CFR_CONFIG_REQ_MST = 0x00400000,
        CFG_CONFIG_REQ_SLV = 0x00800000,
        CFG_SET_STD_CONFIG = 0x01000000,

        /*
         *  ISR Register bit fields 
         *  -------------------------------------------------------
         *  Bits   | Description                   | Access mode |
         *  -------------------------------------------------------
         *  [0]    | Overflow error interrupt      | R           |
         *  [1]    | Parity error interrupt        | R           |
         *  [2]    | Frame error interrupt         | R           |
         *  [3]    | Configuration error interrupt | R           |
         *  [31:4] | Reserved                      | NONE        |
         *  -------------------------------------------------------
         */
        
        ISR_OVERFLOW_ERROR = 0x00000001,
        ISR_PARITY_ERROR = 0x00000002,
        ISR_FRAME_ERROR = 0x00000003,
        ISR_CONFIG_ERROR = 0x00000004,

        /* 
         *  IMR Register bit fields 
         *  --------------------------------------------------------------
         *  Bits   | Description                          | Access mode |
         *  --------------------------------------------------------------
         *  [0]    | Overflow error interrupt enable      | W / R       |
         *  [1]    | Parity error interrupt enable        | W / R       |
         *  [2]    | Frame error interrupt enable         | W / R       |
         *  [3]    | Configuration error interrupt enable | W / R       | 
         *  [31:4] | Reserved                             | NONE        |
         *  -------------------------------------------------------------- 
         */ 

        IMR_OVERFLOW_ENABLE = 0x00000001,
        IMR_PARITY_ENABLE = 0x00000002,
        IMR_FRAME_ENABLE = 0x00000003,
        IMR_CONFIG_ENABLE = 0x00000004,

        /* 
         *  RXR Register bit fields 
         *  ---------------------------------------------------------------
         *  Bits    | Description                          | Access mode |
         *  ---------------------------------------------------------------
         *  [7:0]   | Received data                        | R           |
         *  [8]     | FIFO RX full                         | R           |
         *  [9]     | FIFO RX empty                        | R           |
         *  [31:10] | Reserved                             | NONE        |
         *  ---------------------------------------------------------------
         */ 

        RXR_DATA_RX = 0x000000FF,
        RXR_FIFO_RX_FULL = 0x00000100,
        RXR_FIFO_RX_EMPTY = 0x00000200,

        /* 
         *  TXR Register bit fields 
         *  ---------------------------------------------------------------
         *  Bits    | Description                          | Access mode |
         *  ---------------------------------------------------------------
         *  [7:0]   | Data to be send                      | W           |
         *  [8]     | FIFO TX full                         | R           |
         *  [9]     | FIFO TX empty                        | R           |
         *  [31:10] | Reserved                             | NONE        |
         *  ---------------------------------------------------------------
         */ 

        TXR_DATA_TX = 0x000000FF,
        TXR_FIFO_TX_FULL = 0x00000100,
        TXR_FIFO_TX_EMPTY = 0x00000200,

        /* 
         *  IDR Register bit fields 
         *  ----------------------------------------------------------------
         *  Bits    | Description                           | Access mode |
         *  ----------------------------------------------------------------
         *  [15:0]  | Creator's device initials (GT) in hex | R           |
         *  [23:16] | Product number                        | R           |
         *  [31:24] | Device's number in the system         | R           | 
         *  ----------------------------------------------------------------  
         */

        IDR_CDI = 0x0000FFFF,
        IDR_PROD_NUM = 0x00FF0000,
        IDR_DEV_NUM = 0xFF000000
    };

    /*  Data width configuration code  */
    enum {
        DW_BIT5 = 0b00,
        DW_BIT6 = 0b01,
        DW_BIT7 = 0b10,
        DW_BIT8 = 0b11
    };

    /*  Stop bits number configuration code  */
    enum {
        SB_BIT1 = 0b00,
        SB_BIT15 = 0b01,
        SB_RESERVED = 0b10,
        SB_BIT2 = 0b11 
    };

    /*  Parity mode configuration code  */
    enum {
        DISABLED1 = 0b00,
        EVEN = 0b01,
        DISABLED2 = 0b10,
        ODD = 0b11
    };
    

    public:

        //----------------//
        //  CONSTRUCTORS  //
        //----------------//

        /*  
         *  This constructor initialize the device giving it a base address and setting up the configuration,
         *  which is specified by the user.
         */
        UartCore(uint32_t baseAddr, uint16_t baudRate, uint32_t dataWidth, uint32_t stopBits, uint32_t parityMode);     // DONE

        /*
         *  This constructor initialize the device giving it a base address specified by the user. The device is 
         *  then set up with the standard configuration (see #define section).
         */
        UartCore(uint32_t baseAddr);    // DONE

        /*
         *  Get base address of the device. Multiple UART can exist in a system so they have different addresses.
         */
        uint32_t getBaseAddress();


        //-----------------//
        //  SET BAUD RATE  //
        //-----------------//

        /*
         *  Set the baud rate given a specified system clock frequency.
         */
        void UART_setBaudRate(uint32_t baudRate);   // DONE


        //------------------//
        //  RX FIFO STATUS  //
        //------------------//

        /* 
         *  Check if the receiver FIFO is full.  
         */
        bool UART_RxFull();

        /*  
         *  Check if the receiver FIFO is empty.  
         */
        bool UART_RxEmpty();


        //------------------//
        //  TX FIFO STATUS  //
        //------------------//

        /* 
         *  Check if the transmitter FIFO is full.  
         */
        bool UART_TxFull();

        /*  
         *  Check if the transmitter FIFO is empty. 
         */
        bool UART_TxEmpty();


        //-------------------//
        //  BYTE OPERATIONS  //
        //-------------------//

        /*  
         *  Transmit a byte of data. 
         */
        void UART_sendByte(uint8_t data);

        /*  
         *  Retrieve a byte from the UART.  
         */
        uint8_t UART_readByte();

        /* 
         *  Transmit a stream of bytes, it is memorized in an array and the dimension of the stream is
         *  specified by the 'size' parameter.
         */
        void UART_sendByteStream(const uint8_t *stream, size_t size);

        /*
         *  Read a stream of bytes, return it as an array, the dimension of the stream is specified
         *  by the 'size' parameter. 
         */
        uint8_t* UART_readByteStream(size_t size);


        //------------------------//
        //  CHARACTER OPERATIONS  //
        //------------------------//

        /*  
         *  Transmit a character.  
         */
        void UART_sendChar(char data);

        /*  
         *  Retrieve a character from the UART.  
         */
        char UART_readChar();

        /*  
         *  Transmit a string.  
         */
        void UART_sendString(const char *string);

        /*  
         *  Read a string.  
         */
        char* UART_readString();


        //---------------//
        //  UART ERRORS  //
        //---------------//

        bool UART_getOverflowError();

        bool UART_getFrameError();

        bool UART_getParityError();

        bool UART_getConfigurationError();
        
        /*  
         *  Read the ISR register, return an int that has the same value of the ISR.  
         */
        uint32_t UART_getErrors();


        //----------------------//
        //  UART CONFIGURATION  //
        //----------------------//

        uint32_t UART_getDataWidth();

        uint32_t UART_getParityMode();

        uint32_t UART_getStopBitsNumber();
        
        /*  
         *  Read the CFR register, return an int that has the same value of the CFR [21:16].  
         */
        uint32_t UART_getConfig();


        /*
         *  Send a configuration request and a stream of configuration packets to the slave device, 
         *  the function returns true or false if the configuration was succesful or not.
         */
        bool UART_configureDevice(uint8_t dataWidthID, uint8_t parityModeID, uint8_t stopBitsNumID);


        //--------------------//
        //  ENABLE INTERRUPT  //
        //--------------------//

        /*
         *  Enable or disable the interrupt generation on a specified error occurance. 
         */

        void UART_setIntOverflowError(bool enable);

        void UART_setIntFrameError(bool enable);

        void UART_setIntParityError(bool enable);

        void UART_setIntConfigError(bool enable);



    private:

        /*
         *  Base address of the UART device.
         */
        uint32_t baseAddress;
        
        /*
         *  Tell to the UART to send a configuration request signal (in this case the device acts like a master).
         */
        void UART_sendConfigReq();      // DONE

        /*
         *  Check if the other device has requested a configuration 
         */
        bool UART_checkConfigReq();     // DONE


        //-------------------------//
        //  CONFIGURATION PACKETS  //
        //-------------------------//

        /*
         *  Send a configuration packet, option is specified in function's parameter. 
         *  These functions are legal only when the device is in configuration mode.
         */
        void UART_sendDataWidthPacket(uint32_t configCode);     // DONE

        void UART_sendParityModePacket(uint32_t configCode);    // DONE

        void UART_sendStopBitsNumberPacket(uint32_t configCode);    // DONE

        void UART_sendEndConfigurationPacket();   // DONE

};

#endif