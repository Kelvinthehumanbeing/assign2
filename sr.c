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

static struct pkt buffer[WINDOWSIZE];                   /* array for storing packets waiting for ACK */
static bool acked[WINDOWSIZE];                          /* track if a packet has been acknowledged */
static int windowfirst, windowlast;                     /* array index of the first/last packet in window */
static int windowcount;                                 /* the number of packets currently in window */
static int A_nextseqnum;                                /* the next sequence number to be used by the sender */


/* called from layer 5 (application layer), passed the message to be sent to other side */
void A_output(struct msg message)
{
  struct pkt sendpkt;
  int i;

  /* if not blocked waiting on ACK */
  if (windowcount < WINDOWSIZE) {
    if (TRACE > 1)
      printf("----A: New message arrives, send window is not full, send new messge to layer3!\n");

    /* create packet */
    sendpkt.seqnum = A_nextseqnum;
    sendpkt.acknum = NOTINUSE;
    for (i=0; i<20; i++)
      sendpkt.payload[i] = message.data[i];
    sendpkt.checksum = ComputeChecksum(sendpkt);

    /* put packet in window buffer */
    windowlast = (windowlast + 1) % WINDOWSIZE;
    buffer[windowlast] = sendpkt;
    acked[windowlast] = false;
    windowcount++;

    /* send packet */
    if (TRACE > 0)
      printf("Sending packet %d to layer 3\n", sendpkt.seqnum);
    tolayer3(A, sendpkt);

    /* start timer if first packet in window */
    if (windowcount == 1)
      starttimer(A, RTT);

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

/* called from layer 3, when a packet arrives for layer 4 */
void A_input(struct pkt packet)
{
  int i;

  /* if received ACK is not corrupted */ 
  if (!IsCorrupted(packet)) {
    if (TRACE > 0)
      printf("----A: uncorrupted ACK %d is received\n",packet.acknum);
    total_ACKs_received++;

    /* check if new ACK */
    if (windowcount != 0) {
      /* find the packet in window */
      for (i = 0; i < windowcount; i++) {
        int slot = (windowfirst + i) % WINDOWSIZE;
        if (buffer[slot].seqnum == packet.acknum && !acked[slot]) {
          acked[slot] = true;
          /* packet is a new ACK */
          if (TRACE > 0)
            printf("----A: ACK %d is not a duplicate\n",packet.acknum);
          new_ACKs++;

          /* slide window if it's the first packet */
          while (windowcount > 0 && acked[windowfirst]) {
            acked[windowfirst] = false;
            windowfirst = (windowfirst + 1) % WINDOWSIZE;
            windowcount--;
          }
          break;
        }
      }
      /* After sliding window, restart timer if there are still outstanding packets */
      if (windowcount > 0) {
        stoptimer(A);
        starttimer(A, RTT);
      } else {
        stoptimer(A);
      }
    }
  }
  else {
    if (TRACE > 0)
      printf("----A: corrupted ACK is received, do nothing!\n");
  }
}

/* called when A's timer goes off */
void A_timerinterrupt(void)
{
  if (TRACE > 0)
    printf("----A: time out,resend packets!\n");

  /* resend the earliest unACKed packet */
  if (windowcount > 0) {
    if (TRACE > 0)
      printf("---A: resending packet %d\n", buffer[windowfirst].seqnum);
    tolayer3(A, buffer[windowfirst]);
    packets_resent++;
    /* restart timer for this earliest unACKed packet */
    starttimer(A, RTT);
  }
}

/* the following routine will be called once (only) before any other */
/* entity A routines are called. You can use it to do any initialization */
void A_init(void)
{
  /* initialise A's window, buffer and sequence number */
  A_nextseqnum = 0;  /* A starts with seq num 0, do not change this */
  windowfirst = 0;
  windowlast = -1;
  windowcount = 0;
  for (int i = 0; i < WINDOWSIZE; i++) {
      acked[i] = false;
  }
}

/********* Receiver (B)  variables and procedures ************/

static int rcv_base;      /* base sequence number of receiving window */
static int B_nextseqnum;  /* the sequence number for the next packets sent by B */
static bool received[SEQSPACE];         /* tracks received sequence numbers */
static struct pkt rcv_buffer[SEQSPACE]; /* buffer for storing received packets */

/* called from layer 3, when a packet arrives for layer 4 at B*/
void B_input(struct pkt packet)
{
  struct pkt sendpkt;
  int i;

  if (!IsCorrupted(packet)) {
    int offset = (packet.seqnum - rcv_base + SEQSPACE) % SEQSPACE;
    if (offset < WINDOWSIZE) {
      if (!received[packet.seqnum]) {
        received[packet.seqnum] = true;
        rcv_buffer[packet.seqnum] = packet;
        if (TRACE > 0)
          printf("----B: packet %d is correctly received, send ACK!\n",packet.seqnum);
        packets_received++;
      }

      while (received[rcv_base]) {
        tolayer5(B, rcv_buffer[rcv_base].payload);
        received[rcv_base] = false;
        rcv_base = (rcv_base + 1) % SEQSPACE;
      }

      /* send ACK */
      sendpkt.acknum = packet.seqnum;
    } else {
      /* packet outside window - send ACK for the last in-order packet */
      if (TRACE > 0)
        printf("----B: packet corrupted or not expected sequence number, resend ACK!\n");
      sendpkt.acknum = (rcv_base - 1 + SEQSPACE) % SEQSPACE;
    }
  } else {
    /* packet is corrupted - send ACK for the last in-order packet */
    if (TRACE > 0)
      printf("----B: packet corrupted or not expected sequence number, resend ACK!\n");
    sendpkt.acknum = (rcv_base - 1 + SEQSPACE) % SEQSPACE;
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
  rcv_base = 0;
  B_nextseqnum = 1;
  for (int i = 0; i < SEQSPACE; i++) {
    received[i] = false;
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

