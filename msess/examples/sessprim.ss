/**

============================= 1 ============================
Send/Receive where the means for transmission are channels:
each two roles/process who are communicating with each other
do so by using an exclusive channel

*/

void send (Channel c, Dyn t msg)
  requires c::Chan<ms> * ms::Sess<c!L(msg);rest> * L(msg)
  ensures  c::Chan<ms> * ms::Sess<rest>;

void send (Channel c, Dyn t msg)
  requires c::Chan<ms> * ms::Sess<c!L1(msg);rest1 or c!L2(msg);rest2> * L1(msg) or
           c::Chan<ms> * ms::Sess<c!L1(msg);rest1 or c!L2(msg);rest2> * L2(msg)
  ensures  c::Chan<ms>;

void send (Channel c, Dyn t msg)
  requires c::Chan<ms> * ms::Sess<c!L(msg)> * L(msg)
  ensures  c::Chan<ms>;
  
Dyn t receive (Channel c)
  requires Chan<c, ms> * ms::Sess<c?L(msg);rest> 
  ensures  Chan<c, ms> * ms::Sess<rest> * L(res);

  requires Chan<c, ms> * ms::Sess<c?L1(msg);rest1 or c?L2(msg);rest2> 
  ensures  Chan<c, ms> * ms::Sess<rest1> * L1(res)
        or Chan<c, ms> * ms::Sess<rest2> * L2(res);

  requires Chan<c, ms> * ms::Sess<c?L(msg)> 
  ensures  Chan<c, ms> * L(res);

c::Chan<ms> * ms::Sess{c!1;;c!Addr;;c?Date or c!0)}<> & msg = 1
|-
c::Chan<ms> * ms::Sess<c!L1(msg);rest1 or c!L2(msg);rest2> * L1(msg) or
c::Chan<ms> * ms::Sess<c!L1(msg);rest1 or c!L2(msg);rest2> * L2(msg).


===================================================
================ RECEIVE ==========================
===================================================
Dyn t receive (Channel c) \Pre \Post
\Pre:  Chan(c,ms) * ms::Sess<c?L(msg)> 
\Post: Chan(c,ms) * L(res);

\foreach i Chan(k,s)*Sess(s,(k?P_i(a)*S1_i;S2_i)*S1;S2) |- \Pre * R_i(L)
--------------------------------------------------------------------------------
|- {Chan(k,s)*Sess(s,(OR_i k?P_i(a)*S1_i;S2_i)*S1;S2)} v = receive(k); {OR_i R_i(L)*\Post}

/**

============================= 2 ============================
Send/Receive where the means for transmission are FIFO queues:
each role has an associated queue

*/
