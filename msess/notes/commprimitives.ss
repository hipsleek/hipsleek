/**

============================= 1 ============================
Send/Receive where the means for transmission are channels:
each two roles/process who are communicating with each other
do so by using an exclusive channel

*/

/* void send (Channel c, Dyn t x) */
/*   requires c::Chan<!x.%L;%rest> * %L // & x=msg */
/*   ensures  c::Chan<%rest>; */

/* void send (Channel c, Dyn t x) */
/*   requires c::Chan<!m.L(m);%rest> * L(x) // & x=msg */
/*   ensures  c::Chan<%rest>; */



/* Dyn t receive (Channel c) */
/*      requires Chan<c, ?msg.L(msg);rest>  */
/*   ensures  Chan<c, rest> * L(res); //& msg=res; */


void send (Channel c, int x)
  requires c::Chan{@S !v#%L(v);;%R}<this> * %L(x)
  ensures  c::Chan{@S %R}<this>;

/* v is existential, so I cannot use it inside the post */
int receive (Channel c)
  /* requires c::Chan{@S ?v#%L(v) & v=a;;%R}<this> */
  /* ensures  c::Chan{@S %R}<this> * %L(a) & a=res; */
  requires c::Chan{@S ?v#%L(v);;%R}<this>
  ensures  c::Chan{@S %R}<this> * %L(res);


  
/**

============================= 2 ============================
Send/Receive where the means for transmission are FIFO queues:
each role has an associated queue

*/



