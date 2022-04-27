// MIT License
//
// Copyright (c) 2021 Gabriele Tripi
// 
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
// 
// The above copyright notice and this permission notice shall be included in all
// copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.
// ------------------------------------------------------------------------------------
// ------------------------------------------------------------------------------------
// FILE NAME : fsm_pkg.sv
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// ------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : This package contains enumerations and parameters for the various FSMs
//               contained in the modules.  
// ------------------------------------------------------------------------------------
// KEYWORDS : GENERAL, MAIN CONTROLLER, RECEIVER, TRANSMITTER
// ------------------------------------------------------------------------------------

`ifndef FSM_PKG
  `define FSM_PKG

package fsm_pkg;

//-----------//
//  GENERAL  //
//-----------//

  /* Next and current state */
  localparam NXT = 1;
  localparam CRT = 0;


//-------------------//
//  MAIN CONTROLLER  //
//-------------------//

  typedef enum logic [3:0] {
    /*
     * Send configuration request to slave device 
     */ 
    CFG_REQ_MST,

    /* 
     * If the device sees the initialization signal (10ms RX low) then send an acknowledgment packet 
     */
    SEND_ACKN_SLV,

    /* 
     * Drive TX low to send the initialization signal 
     */
    SETUP_SLV,

    /* 
     * Send configuration packets
     */ 
    SETUP_MST,

    /* 
     * Wait transmitter to end the request or a configuration
     */
    WAIT_TX_MST,

    /*
     * Wait transmitter to end sending acknowledgment packet 
     */
    WAIT_TX_SLV,

    /* 
     * Wait request acknowledgment 
     */
    WAIT_REQ_ACKN_MST,

    /* 
     * Wait for the slave acknowledgment for the configuration packet received
     */
    WAIT_ACKN_MST,

    /*
     * Set the device in standard configuration
     */
    STD_CONFIG,

    /* 
     * UART's main state 
     */
    MAIN
  } main_control_fsm_e;


//------------//
//  RECEIVER  //
//------------//

  /* TX line in idle state */
  localparam RX_LINE_IDLE = 1;

  typedef enum logic [2:0] {
    /* 
     * The device is waiting for data
     */
    RX_IDLE,

    /* 
     * The device is receiving a configuration request 
     */

    RX_CONFIG_REQ,

    /* 
     * Sample start bit 
     */
    RX_START,

    /* 
     * Sample the data bits
     */
    RX_SAMPLE,

    /* 
     * Sample parity bit 
     */
    RX_PARITY,

    /* 
     * Sample stop bits to end the transaction 
     */
    RX_DONE
  } receiver_fsm_e;


//---------------//
//  TRANSMITTER  //
//---------------//

  /* TX line in idle state */
  localparam TX_LINE_IDLE = 1;

  typedef enum logic [2:0] {
    /*
     * The device is waiting for data 
     */
    TX_IDLE,

    /* 
     * Send a configuration request 
     */
    TX_CFG_REQ,

    /* 
     * Inform the other device that data is arriving
     * by sending a start bit 
     */
    TX_START,

    /* 
     * Transmit the data bits serially to the other device
     */
    TX_DATA,

    /* 
     * Transmit parity bit 
     */
    TX_PARITY,

    /* 
     * Send stop bits to end the transaction 
     */
    TX_DONE
  } transmitter_fsm_e;

endpackage : fsm_pkg

`endif