/* hip_include 'msess/notes/node.ss' */
/**

============================= 1 ============================
Send/Receive where the means for transmission are channels:
each two roles/process who are communicating with each other
do so by using an exclusive channel

*/

/**
 int
*/
void send (Channel c, int x)
  requires c::Chan{@S !v#%L(v);;%R}<> * %L(x)
  ensures  c::Chan{@S %R}<>;

int receive (Channel c)
  requires c::Chan{@S ?v#%L(v);;%R}<>
  ensures  c::Chan{@S %R}<> * %L(res);


/**
 Channel
*/
void sendc (Channel c, Channel x)
  requires c::Chan{@S !v#%L(v);;%R}<> * %L(x)
  ensures  c::Chan{@S %R}<>;

Channel receivec (Channel c)
  requires c::Chan{@S ?v#%L(v);;%R}<>
  ensures  c::Chan{@S %R}<> * %L(res);

/**
   Addr
*/
void senda (Channel c, Addr x)
  requires c::Chan{@S !v#%L(v);;%R}<> * %L(x)
  ensures  c::Chan{@S %R}<>;

Addr receivea (Channel c)
  requires c::Chan{@S ?v#%L(v);;%R}<>
  ensures  c::Chan{@S %R}<> * %L(res);


/**
   Date
*/
void sendd (Channel c, DDate x)
  requires c::Chan{@S !v#%L(v);;%R}<> * %L(x)
  ensures  c::Chan{@S %R}<>;

DDate received (Channel c)
  requires c::Chan{@S ?v#%L(v);;%R}<>
  ensures  c::Chan{@S %R}<> * %L(res);
  
/**

============================= 2 ============================
Send/Receive where the means for transmission are FIFO queues:
each role has an associated queue

*/



