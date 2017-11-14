hip_include 'msess/notes/node.ss'
hip_include 'msess/notes/hodef.ss'
hip_include 'msess/notes/commprimitives.ss'

/* S - server, C - client
   ms -  server's mailbox
   mc -  client's mailbox
*/
pred_sess_prot G<S:role,C:role,ms:chan,mc:chan> == C->S:ms(1) ;; S->C:mc(v#v>0);

int foo(int x)
  requires x>0
  ensures  res = x + x;

/*
   c1 -  server's mailbox
   c2 -  client's mailbox
*/
void server(Channel c1, Channel c2)
  requires c1::Chan{@S G<S@peer,C,c1@chan,c2>}<S> * c2::Chan{@S G<S@peer,C,c1,c2@chan>}<S>
  ensures  c1::Chan{@S emp}<S> * c2::Chan{@S emp}<S>;
  {
    assume S::Peer<>;
    int x = receive(c1);
    int y = foo(x);
    send(c2,y);
    dprint;
  }

void client(Channel c1, Channel c2)
  requires c1::Chan{@S G<S,C@peer,c1@chan,c2>}<C> * c2::Chan{@S G<S,C@peer,c1,c2@chan>}<C>
  ensures  c1::Chan{@S emp}<C> * c2::Chan{@S emp}<C>;
  {
    assume C::Peer<>;
    send(c1,1);
    int y = receive(c2);
    dprint;
  }


void client_buggy(Channel c1, Channel c2)
  requires c1::Chan{@S G<S,C@peer,c1@chan,c2>}<C> * c2::Chan{@S G<S,C@peer,c1,c2@chan>}<C>
  ensures  c1::Chan{@S emp}<C> * c2::Chan{@S emp}<C>;
  {
    //swap send & recv
    int y = receive(c2);
    send(c1,1);
    dprint;
  }


int goo(node x, int c)
  requires x::node<c,d>
  ensures true;


/*  void main(node x ) */
/*     requires [H,C,S,P,ms,mc] H::GLOB{ H::G<S,C,ms,mc>}<P,{ms,mc}> & P={C,S} & ms!=mc & C!=S */
/*    /\* requires [G,C,S,P,ms,mc] G::INITALL<{ms,mc}> & P={C,S} & ms!=mc & C!=S *\/ */
/*    ensures  true; */
/* { */
/*   Channel c1 = open () with (mc,P,G); */
/*   Channel c2 = open () with (ms,P,G); */
  
  
/* } */

void main(node x )
   requires [H,C,S,P,ms,mc] H::GLOB{ H::G<S,C,ms,mc>}<P,{ms,mc}> & P={C,S} & ms!=mc & C!=S
   /* requires [H,C,S,P,ms,mc] H::INITALL<{ms,mc}> & P={C,S} & ms!=mc & C!=S */
   ensures  true; 
{
  dprint;
  Channel c1 = open () with (mc,P,H);
  dprint;
  Channel c2 = open () with (ms,P,H);
  dprint;
}
