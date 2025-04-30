#include <stdlib.h>
#include <stdio.h>
#include <stdbool.h>
#include "emulator.h"
#include "gbn.h"

/* ******************************************************************
   Selective Repeat protocol implementation
*********************************************************************/

#define RTT  16.0       /* round trip time.  MUST BE SET TO 16.0 when submitting assignment */
#define WINDOWSIZE 6    /* the maximum number of buffered unacked packet */
#define SEQSPACE 12     /* the sequence space must be twice the window size for SR */
#define NOTINUSE (-1)   /* used to fill header fields that are not being used */

/* packet status for sender window slots */
#define PKT_EMPTY 0     /* slot is empty */
#define PKT_SENT 1      /* packet is sent, waiting for ACK */
#define PKT_ACKED 2     /* packet is ACKed */

/* structure to store packet information in sender window */
struct sender_slot {
    struct pkt packet;  /* the actual packet */
    int status;         /* status of this slot: EMPTY/SENT/ACKED */
    double timer;       /* when this packet was sent (for timeout) */
};

/* structure to store packet information in receiver window */
struct receiver_slot {
    struct pkt packet;  /* the actual packet */
    bool received;      /* whether packet has been received */
};

/* generic procedure to compute the checksum of a packet.  Used by both sender and receiver  
   the simulator will overwrite part of your packet with 'z's.  It will not overwrite your 
   original checksum.  This procedure must generate a different checksum to the original if
   the packet is corrupted.
*/
int ComputeChecksum(struct pkt packet)
{
  int checksum = 0;
  int i;

  checksum = packet.seqnum;
  checksum += packet.acknum;
  for ( i=0; i<20; i++ ) 
    checksum += (int)(packet.payload[i]);

  return checksum;
}

bool IsCorrupted(struct pkt packet)
{
  if (packet.checksum == ComputeChecksum(packet))
    return (false);
  else
    return (true);
}


/********* Sender (A) variables and functions ************/

static struct sender_slot sender_window[WINDOWSIZE];    /* array for storing packets waiting for ACK */
static int windowfirst;                                 /* array index of the first packet in window */
static int windowlast;                                  /* array index of the last packet in window */
static int windowcount;                                 /* the number of packets currently in window */
static int A_nextseqnum;                                /* the next sequence number to be used by the sender */


/* called from layer 5 (application layer), passed the message to be sent to other side */
void A_output(struct msg message)
{
  struct pkt sendpkt;
  int i;

  /* if not blocked waiting on ACK */
  if ( windowcount < WINDOWSIZE) {
    if (TRACE > 1)
      printf("----A: New message arrives, send window is not full, send new messge to layer3!\n");

    /* create packet */
    sendpkt.seqnum = A_nextseqnum;
    sendpkt.acknum = NOTINUSE;
    for ( i=0; i<20 ; i++ ) 
      sendpkt.payload[i] = message.data[i];
    sendpkt.checksum = ComputeChecksum(sendpkt); 

    /* put packet in window buffer */
    windowlast = (windowlast + 1) % WINDOWSIZE; 
    sender_window[windowlast].packet = sendpkt;
    sender_window[windowlast].status = PKT_SENT;
    windowcount++;

    /* send out packet */
    if (TRACE > 0)
      printf("Sending packet %d to layer 3\n", sendpkt.seqnum);
    tolayer3(A, sendpkt);

    /* start timer for this packet */
    starttimer(A,RTT);

    /* get next sequence number, wrap back to 0 */
    A_nextseqnum = (A_nextseqnum + 1) % SEQSPACE;  
  }
  /* if blocked, window is full */
  else {
    if (TRACE > 0)
      printf("----A: New message arrives, send window is full\n");
    window_full++;
  }
}


/* called from layer 3, when a packet arrives for layer 4 
   In this practical this will always be an ACK as B never sends data.
*/
void A_input(struct pkt packet)
{
  int i;

  /* if received ACK is not corrupted */ 
  if (!IsCorrupted(packet)) {
    if (TRACE > 0)
      printf("----A: uncorrupted ACK %d is received\n",packet.acknum);
    total_ACKs_received++;

    /* find the packet in window */
    for (i = 0; i < WINDOWSIZE; i++) {
      if (sender_window[i].status == PKT_SENT && 
          sender_window[i].packet.seqnum == packet.acknum) {
        /* mark packet as acked */
        sender_window[i].status = PKT_ACKED;
        new_ACKs++;
        
        if (TRACE > 0)
          printf("----A: ACK %d is not a duplicate\n",packet.acknum);

        /* stop timer for this packet */
        stoptimer(A);

        /* if this is base packet, slide window */
        if (i == windowfirst) {
          while (windowcount > 0 && sender_window[windowfirst].status == PKT_ACKED) {
            sender_window[windowfirst].status = PKT_EMPTY;
            windowfirst = (windowfirst + 1) % WINDOWSIZE;
            windowcount--;
          }
        }

        /* restart timer if there are unacked packets */
        if (windowcount > 0) {
          starttimer(A, RTT);
        }
        break;
      }
    }
    if (i == WINDOWSIZE && TRACE > 0)
      printf("----A: duplicate ACK received, do nothing!\n");
  }
  else {
    if (TRACE > 0)
      printf("----A: corrupted ACK is received, do nothing!\n");
  }
}

/* called when A's timer goes off */
void A_timerinterrupt(void)
{
  int i;

  if (TRACE > 0)
    printf("----A: time out,resend packets!\n");

  /* resend all unacked packets in window */
  for (i = 0; i < WINDOWSIZE; i++) {
    if (sender_window[i].status == PKT_SENT) {
      if (TRACE > 0)
        printf("---A: resending packet %d\n", sender_window[i].packet.seqnum);
      tolayer3(A, sender_window[i].packet);
      packets_resent++;
    }
  }

  /* restart timer */
  if (windowcount > 0)
    starttimer(A, RTT);
}

/* the following routine will be called once (only) before any other */
/* entity A routines are called. You can use it to do any initialization */
void A_init(void)
{
  int i;
  /* initialise A's window, buffer and sequence number */
  A_nextseqnum = 0;  /* A starts with seq num 0, do not change this */
  windowfirst = 0;
  windowlast = -1;
  windowcount = 0;

  /* initialize sender window */
  for (i = 0; i < WINDOWSIZE; i++) {
    sender_window[i].status = PKT_EMPTY;
  }
}



/********* Receiver (B)  variables and procedures ************/

static struct receiver_slot receiver_window[WINDOWSIZE];  /* buffer for out of order packets */
static int rcv_base;      /* base sequence number of receiving window */
static int B_nextseqnum;  /* the sequence number for the next packets sent by B */

/* called from layer 3, when a packet arrives for layer 4 at B*/
void B_input(struct pkt packet)
{
  struct pkt sendpkt;
  int i;

  /* if not corrupted and received packet is in window range */
  if (!IsCorrupted(packet)) {
    int offset = (packet.seqnum - rcv_base + SEQSPACE) % SEQSPACE;
    
    if (offset < WINDOWSIZE) {
      if (TRACE > 0)
        printf("----B: packet %d is correctly received, send ACK!\n", packet.seqnum);
      
      /* store packet in receiver window */
      receiver_window[offset].packet = packet;
      receiver_window[offset].received = true;
      
      /* if this is the base, deliver it and any consecutive packets */
      if (offset == 0) {
        while (offset < WINDOWSIZE && receiver_window[offset].received) {
          tolayer5(B, receiver_window[offset].packet.payload);
          receiver_window[offset].received = false;
          offset++;
          rcv_base = (rcv_base + 1) % SEQSPACE;
          packets_received++;
        }
      }
      
      /* send ACK */
      sendpkt.acknum = packet.seqnum;
    } else {
      /* packet outside window - send ACK for last in-order packet */
      if (TRACE > 0)
        printf("----B: packet %d outside window, resend ACK!\n", packet.seqnum);
      sendpkt.acknum = ((rcv_base - 1) + SEQSPACE) % SEQSPACE;
    }
  } else {
    /* packet is corrupted - send ACK for last in-order packet */
    if (TRACE > 0)
      printf("----B: packet corrupted or not expected sequence number, resend ACK!\n");
    sendpkt.acknum = ((rcv_base - 1) + SEQSPACE) % SEQSPACE;
  }

  /* create packet */
  sendpkt.seqnum = B_nextseqnum;
  B_nextseqnum = (B_nextseqnum + 1) % 2;
    
  /* we don't have any data to send. fill payload with 0's */
  for (i=0; i<20; i++)
    sendpkt.payload[i] = '0';

  /* compute checksum */
  sendpkt.checksum = ComputeChecksum(sendpkt);

  /* send out packet */
  tolayer3(B, sendpkt);
}

/* the following routine will be called once (only) before any other */
/* entity B routines are called. You can use it to do any initialization */
void B_init(void)
{
  int i;
  rcv_base = 0;
  B_nextseqnum = 1;
  
  /* initialize receiver window */
  for (i = 0; i < WINDOWSIZE; i++) {
    receiver_window[i].received = false;
  }
}

/******************************************************************************
 * The following functions need be completed only for bi-directional messages *
 *****************************************************************************/

/* Note that with simplex transfer from a-to-B, there is no B_output() */
void B_output(struct msg message)  
{
}

/* called when B's timer goes off */
void B_timerinterrupt(void)
{
}

