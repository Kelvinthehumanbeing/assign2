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
  int i, j;
  struct pkt packet;
  bool found_empty = false;

  /* if window is not full */
  if (windowcount < WINDOWSIZE) {
    if (TRACE > 0)
      printf("----A: New message arrives, send window is not full, send new messge to layer3!\n");

    /* find an empty slot in window */
    for (i = 0; i < WINDOWSIZE && !found_empty; i++) {
      int slot = (windowfirst + i) % WINDOWSIZE;
      if (sender_window[slot].status == PKT_EMPTY) {
        found_empty = true;
        /* create packet */
        packet.seqnum = A_nextseqnum;
        packet.acknum = NOTINUSE;
        for (j = 0; j < 20; j++)
          packet.payload[j] = message.data[j];
        packet.checksum = ComputeChecksum(packet);

        /* store packet in window */
        sender_window[slot].packet = packet;
        sender_window[slot].status = PKT_SENT;
        windowcount++;
        A_nextseqnum = (A_nextseqnum + 1) % SEQSPACE;

        /* send packet */
        if (TRACE > 0)
          printf("Sending packet %d to layer 3\n", packet.seqnum);
        tolayer3(A, packet);

        /* start timer if this is the first packet in window */
        if (windowcount == 1) {
          starttimer(A, RTT);
        }
      }
    }
  }
  else {
    if (TRACE > 0)
      printf("----A: New message arrives, send window is full\n");
    window_full++;
  }
}


/* called from layer 3, when a packet arrives for layer 4 */
void A_input(struct pkt packet)
{
  int i;
  bool found = false;

  /* if received ACK is not corrupted */ 
  if (!IsCorrupted(packet)) {
    if (TRACE > 0)
      printf("----A: uncorrupted ACK %d is received\n",packet.acknum);
    total_ACKs_received++;

    /* find the packet in window */
    for (i = 0; i < windowcount; i++) {
      int slot = (windowfirst + i) % WINDOWSIZE;
      if (sender_window[slot].status == PKT_SENT && 
          sender_window[slot].packet.seqnum == packet.acknum) {
        found = true;
        /* mark packet as acked */
        sender_window[slot].status = PKT_ACKED;
        new_ACKs++;
        
        if (TRACE > 0)
          printf("----A: ACK %d is not a duplicate\n",packet.acknum);

        /* slide window if possible */
        while (windowcount > 0 && sender_window[windowfirst].status == PKT_ACKED) {
          sender_window[windowfirst].status = PKT_EMPTY;
          windowfirst = (windowfirst + 1) % WINDOWSIZE;
          windowcount--;
        }

        /* manage timer */
        if (windowcount > 0) {
          stoptimer(A);
          starttimer(A, RTT);
        } else {
          stoptimer(A);
        }
        break;
      }
    }
    if (!found && TRACE > 0)
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
  int slot;
  if (TRACE > 0)
    printf("----A: time out,resend packets!\n");

  /* resend only the first unacked packet in window */
  if (windowcount > 0 && sender_window[windowfirst].status == PKT_SENT) {
    if (TRACE > 0)
      printf("---A: resending packet %d\n", sender_window[windowfirst].packet.seqnum);
    tolayer3(A, sender_window[windowfirst].packet);
    packets_resent++;
    starttimer(A, RTT);
  } else if (windowcount > 0) {
    /* If first packet is not SENT, find the first SENT packet */
    for (i = 0; i < windowcount; i++) {
      slot = (windowfirst + i) % WINDOWSIZE;
      if (sender_window[slot].status == PKT_SENT) {
        if (TRACE > 0)
          printf("---A: resending packet %d\n", sender_window[slot].packet.seqnum);
        tolayer3(A, sender_window[slot].packet);
        packets_resent++;
        starttimer(A, RTT);
        break;
      }
    }
  }
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
        printf("----B: packet %d is correctly received, send ACK!\n",packet.seqnum);
      
      /* store packet in receiver window if not already received */
      if (!receiver_window[offset].received) {
        receiver_window[offset].packet = packet;
        receiver_window[offset].received = true;
        packets_received++;
      }
      
      /* if this is the base, deliver it and any consecutive packets */
      if (offset == 0) {
        while (offset < WINDOWSIZE && receiver_window[offset].received) {
          tolayer5(B, receiver_window[offset].packet.payload);
          receiver_window[offset].received = false;
          offset++;
          rcv_base = (rcv_base + 1) % SEQSPACE;
        }
      }
      
      /* send ACK */
      sendpkt.acknum = packet.seqnum;
    } else {
      /* packet outside window - send ACK for the last in-order packet */
      if (TRACE > 0)
        printf("----B: packet corrupted or not expected sequence number, resend ACK!\n");
      sendpkt.acknum = rcv_base;
    }
  } else {
    /* packet is corrupted - send ACK for the last in-order packet */
    if (TRACE > 0)
      printf("----B: packet corrupted or not expected sequence number, resend ACK!\n");
    sendpkt.acknum = rcv_base;
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

