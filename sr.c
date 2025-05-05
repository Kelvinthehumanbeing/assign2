#include <stdlib.h>
#include <stdio.h>
#include "emulator.h"
#include "gbn.h"


#define true 1
#define false 0

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

int IsCorrupted(struct pkt packet)
{
  if (packet.checksum == ComputeChecksum(packet))
    return (0);
  else
    return (1);
}


/********* Sender (A) variables and functions ************/

static struct pkt buffer[WINDOWSIZE];                   /* array for storing packets waiting for ACK */
static int windowfirst;                                 /* first sequence number in window */
static int windowcount;                                 /* the number of packets currently in window */
static int A_nextseqnum;                                /* the next sequence number to be used by the sender */

/* called from layer 5 (application layer), passed the message to be sent to other side */
void A_output(struct msg message)
{
  struct pkt sendpkt;
  int i;
  int index;
  int seqfirst = windowfirst;
  int seqlast = (windowfirst + WINDOWSIZE - 1) % SEQSPACE;

  /* if the A_nextseqnum is inside the window */
  if (((seqfirst <= seqlast) && (A_nextseqnum >= seqfirst && A_nextseqnum <= seqlast)) ||
      ((seqfirst > seqlast) && (A_nextseqnum >= seqfirst || A_nextseqnum <= seqlast)))
  {
    if (TRACE > 1)
      printf("----A: New message arrives, send window is not full, send new messge to layer3!\n");

    /* create packet */
    sendpkt.seqnum = A_nextseqnum;
    sendpkt.acknum = NOTINUSE;
    for (i=0; i<20; i++)
      sendpkt.payload[i] = message.data[i];
    sendpkt.checksum = ComputeChecksum(sendpkt);

    /* put packet in window buffer */
    if (A_nextseqnum >= seqfirst)
      index = A_nextseqnum - seqfirst;
    else
      index = WINDOWSIZE - seqfirst + A_nextseqnum;
    buffer[index] = sendpkt;
    windowcount++;

    /* send packet */
    if (TRACE > 0)
      printf("Sending packet %d to layer 3\n", sendpkt.seqnum);
    tolayer3(A, sendpkt);

    /* start timer if first packet in window */
    if (A_nextseqnum == seqfirst)
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
  int ackcount = 0;
  int i;
  int seqfirst = windowfirst;
  int seqlast = (windowfirst + WINDOWSIZE - 1) % SEQSPACE;
  int index;

  /* if received ACK is not corrupted */ 
  if (!IsCorrupted(packet)) {
    if (TRACE > 0)
      printf("----A: uncorrupted ACK %d is received\n",packet.acknum);
    total_ACKs_received++;

    /* check if new ACK */
    if (windowcount != 0) {
      /* check case when seqnum has and hasn't wrapped */
      if (((seqfirst <= seqlast) && (packet.acknum >= seqfirst && packet.acknum <= seqlast)) ||
          ((seqfirst > seqlast) && (packet.acknum >= seqfirst || packet.acknum <= seqlast)))
      {
        /* check corresponding position in window buffer */
        if (packet.acknum >= seqfirst)
          index = packet.acknum - seqfirst;
        else
          index = WINDOWSIZE - seqfirst + packet.acknum;

        if (buffer[index].acknum == NOTINUSE) {
          /* packet is a new ACK */
          if (TRACE > 0)
            printf("----A: ACK %d is not a duplicate\n",packet.acknum);
          new_ACKs++;
          windowcount--;
          buffer[index].acknum = packet.acknum;

          /* if it's the base packet */
          if (packet.acknum == seqfirst) {
            /* check how many consecutive acks received in buffer */
            for (i = 0; i < WINDOWSIZE; i++) {
              if (buffer[i].acknum != NOTINUSE && buffer[i].payload[0] != '\0')
                ackcount++;
              else
                break;
            }

            /* slide window */
            windowfirst = (windowfirst + ackcount) % SEQSPACE;

            /* update buffer */
            for (i = 0; i < WINDOWSIZE; i++) {
              if (i + ackcount < WINDOWSIZE)
                buffer[i] = buffer[i + ackcount];
            }

            /* restart timer */
            stoptimer(A);
            if (windowcount > 0)
              starttimer(A, RTT);
          }
        }
        else {
          if (TRACE > 0)
            printf("----A: duplicate ACK received, do nothing!\n");
        }
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
  if (TRACE > 0) {
    printf("----A: time out,resend packets!\n");
    printf("---A: resending packet %d\n", buffer[0].seqnum);
  }
  tolayer3(A, buffer[0]);
  packets_resent++;
  starttimer(A, RTT);
}

/* the following routine will be called once (only) before any other */
/* entity A routines are called. You can use it to do any initialization */
void A_init(void)
{
  /* initialise A's window, buffer and sequence number */
  A_nextseqnum = 0;  /* A starts with seq num 0, do not change this */
  windowfirst = 0;
  windowcount = 0;
}

/********* Receiver (B)  variables and procedures ************/

static struct pkt rcv_buffer[WINDOWSIZE];    /* array for storing packets waiting for packet from A */
static int rcv_base;                         /* first sequence number in receiving window */
static int rcv_last;                         /* last received packet position */

/* called from layer 3, when a packet arrives for layer 4 at B*/
void B_input(struct pkt packet)
{
  struct pkt sendpkt;
  int i;
  int pckcount = 0;
  int seqfirst = rcv_base;
  int seqlast = (rcv_base + WINDOWSIZE - 1) % SEQSPACE;
  int index;

  if (!IsCorrupted(packet)) {
    if (TRACE > 0)
      printf("----B: packet %d is correctly received, send ACK!\n",packet.seqnum);
    packets_received++;

    /* create ACK packet */
    sendpkt.acknum = packet.seqnum;
    sendpkt.seqnum = NOTINUSE;
    for (i=0; i<20; i++)
      sendpkt.payload[i] = '0';
    sendpkt.checksum = ComputeChecksum(sendpkt);
    tolayer3(B, sendpkt);

    /* check if packet is in window */
    if (((seqfirst <= seqlast) && (packet.seqnum >= seqfirst && packet.seqnum <= seqlast)) ||
        ((seqfirst > seqlast) && (packet.seqnum >= seqfirst || packet.seqnum <= seqlast)))
    {
      /* get index in buffer */
      if (packet.seqnum >= seqfirst)
        index = packet.seqnum - seqfirst;
      else
        index = WINDOWSIZE - seqfirst + packet.seqnum;

      /* update rcv_last */
      rcv_last = rcv_last > index ? rcv_last : index;

      /* if not duplicate, save to buffer */
      if (rcv_buffer[index].payload[0] == '\0') {
        rcv_buffer[index] = packet;

        /* if it's the base packet */
        if (packet.seqnum == seqfirst) {
          /* count consecutive received packets */
          for (i = 0; i < WINDOWSIZE; i++) {
            if (rcv_buffer[i].payload[0] != '\0')
              pckcount++;
            else
              break;
          }

          /* update base and buffer */
          rcv_base = (rcv_base + pckcount) % SEQSPACE;
          for (i = 0; i < WINDOWSIZE; i++) {
            if (i + pckcount < WINDOWSIZE)
              rcv_buffer[i] = rcv_buffer[i + pckcount];
          }
        }

        /* deliver to application */
        tolayer5(B, packet.payload);
      }
    }
  }
}

/* the following routine will be called once (only) before any other */
/* entity B routines are called. You can use it to do any initialization */
void B_init(void)
{
  rcv_base = 0;
  rcv_last = -1;
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
