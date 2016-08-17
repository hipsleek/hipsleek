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
  requires c::Chan{@S !v#%L(v);;%rest}<> * %L(x)
  ensures  c::Chan{@S %rest}<>;

int receive (Channel c)
  requires c::Chan{@S ?v#%L(v);;%rest}<> 
  ensures  c::Chan{@S %rest}<> * %L(res); 


  
/**

============================= 2 ============================
Send/Receive where the means for transmission are FIFO queues:
each role has an associated queue

*/



