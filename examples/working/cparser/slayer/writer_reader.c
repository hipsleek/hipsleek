/**
  Copyright (c) Microsoft Corporation.  All rights reserved.


              +-------+
  writer ---> |mailbox| ---> reader
              +-------+

  writer tells reader of mailbox via channel.

  mailbox should be in writer's local-heap.
  It should also be in reader's local-heap: if we take account of expr equality when
  calculating reachability.

  This program should be SAFE: reader should not have mailbox framed-away.

**/


int mailbox;

void writer(int** channel)
/*@
  requires channel::int**<p>
  ensures channel::int**<q>;
*/
{
  mailbox = 1;
  *channel = &mailbox;
}

// mailbox \in footprint.
void reader(int* channel)
/*@
  requires channel::int^<p>
  ensures channel::int^<p>;
*/
{
  int x = *channel;
}

void main()
{
  int* channel;

  writer(&channel);
  // assert ( (channel == &mailbox) && (mailbox == 1) )
  reader(channel);
}
