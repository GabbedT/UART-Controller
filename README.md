# Table of contents
- [Table of contents](#table-of-contents)
- [Introduction](#introduction)
  - [Features](#features)
  - [Block Diagram](#block-diagram)
- [Architecture](#architecture)
  - [Signal Description](#signal-description)
  - [Configuration Protocol](#configuration-protocol)
  - [Main Controller](#main-controller)
  - [Receiver](#receiver)
  - [Transmitter](#transmitter)
  - [Baud Rate Generator](#baud-rate-generator)
  - [Interrupt](#interrupt)
- [Registers](#registers)
  - [Status Register (STR)](#status-register-str)
    - [Fields Description](#fields-description)
  - [Divisor Register (DVR)](#divisor-register-dvr)
  - [FIFO Status Register (FSR)](#fifo-status-register-fsr)
    - [Fields Description](#fields-description-1)
  - [Control Register (CTR)](#control-register-ctr)
    - [Fields Description](#fields-description-2)
  - [Interrupt Status Register (ISR)](#interrupt-status-register-isr)
  - [Data Received Register (RXR)](#data-received-register-rxr)
  - [Data Transmitted Register (TXR)](#data-transmitted-register-txr)
- [Operations](#operations)
  - [Transmission](#transmission)
  - [Reception](#reception)
  - [Data Stream Mode](#data-stream-mode)
  - [Configuration Request](#configuration-request)
- [References](#references)

# Introduction

  ## Features

  ## Block Diagram



# Architecture

  ## Signal Description
  
  ## Configuration Protocol

  ## Main Controller

  ## Receiver

  ## Transmitter
  
  ## Baud Rate Generator

  ## Interrupt 



# Registers

  ## Status Register (STR)

  ![STR](Images/STR.PNG)

  The status register contains the device current configuration except for the baudrate.

  **ADDRESS**: 0

  ### Fields Description

  * **TDSM** : Enable _` data stream mode `_ for transmitter module.
  * **RDSM** : Enable _` data stream mode `_ for receiver module.
  * **SBID** : Set _` stop bit number `_ configuration ID.
    * **00** : 1 stop bit.
    * **01** : 2 stop bits.
    * **10** : Reserved.
    * **11** : Reserved.
  * **PMID** : Set _` parity mode `_ configuration ID.
    * **00** : Even.
    * **01** : Odd.
    * **10** : Disabled.
    * **11** : Disabled. 
  * **DWID** : Set _` data width `_ configuration ID.
    * **00** : 5 bits.
    * **01** : 6 bits.
    * **10** : 7 bits.
    * **11** : 8 bits.


  ## Divisor Register (DVR)

  ![DVR](Images/DVR.PNG)

  The Divisor Register is a 16 bit register splitted in two different addressable register (`LDVR` and `UDVR`). Since the divisor is a 16 bit value and two registers can't be addressed at the same time, to read or write the entire value, two different operation must be executed. 
  
  The UART doesn't change it's configuration until two writes on two the two registers happens.

  **LOWER ADDRESS**: 1  
  **UPPER ADDRESS**: 2


  ## FIFO Status Register (FSR)

  ![FSR](Images/FSR.PNG)

  The FIFO Status Register holds the state of both recever and transmitter FIFOs. Notice how the only useful status flags are: the `full` flag for the transmitter FIFO: the `empty` flag is not really needed because an interrupt will occur when it's empty; the same thing for the `empty` flag for the receiver FIFO: the `full` flag is not really needed because an interrupt will occur when it's full. 

  If the programmer wants the device to interrupt when it receives a fixed amount of data, he can set a threshold for the receiver FIFO buffer.

  ### Fields Description

  * **TXF** : Transmitter FIFO `full` flag.
  * **RXE** : Receiver FIFO `empty` flag.
  * **RX THRESHOLD** : Forces the UART to interrupt when it receives an amount of data that equals that number. Any value between `RX_FIFO_SIZE` and `0` can be set (**those two values are illegal**).


  ## Control Register (CTR)

  ![CTR](Images/CTR.PNG)

  The Control Register controls the state of the configuration request for both master and slave. A bit can also be set to set the device into standard configuration.

  ### Fields Description

  * **CDONE** : The configuration process has ended, this bit **must be polled** during every configuration process (both master and slave).
  * **AKREQ** : Acknowledge the configuration request sended by the master device, the device become slave.
  * **STDC** : Set standard configuration.
  * **SREQ** : Send configuration request, the device in this case become master.

  ## Interrupt Status Register (ISR)

  ## Data Received Register (RXR)

  ## Data Transmitted Register (TXR)



# Operations

  ## Transmission

  ## Reception

  ## Data Stream Mode

  ## Configuration Request 


# References