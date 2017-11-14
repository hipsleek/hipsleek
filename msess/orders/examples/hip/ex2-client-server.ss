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
  requires c1::Chan{@S G<S@peer,C,c1@chan,c2>}<> * c2::Chan{@S G<S@peer,C,c1,c2@chan>}<>
  ensures  c1::Chan{@S emp}<> * c2::Chan{@S emp}<>;
  {
    int x = receive(c1);
    int y = foo(x);
    send(c2,y);
    dprint;
  }

void client(Channel c1, Channel c2)
  requires c1::Chan{@S G<S,C@peer,c1@chan,c2>}<> * c2::Chan{@S G<S,C@peer,c1,c2@chan>}<>
  ensures  c1::Chan{@S emp}<> * c2::Chan{@S emp}<>;
  {
    send(c1,1);
    int y = receive(c2);
    dprint;
  }


void client_buggy(Channel c1, Channel c2)
  requires c1::Chan{@S G<S,C@peer,c1@chan,c2>}<> * c2::Chan{@S G<S,C@peer,c1,c2@chan>}<>
  ensures  c1::Chan{@S emp}<> * c2::Chan{@S emp}<>;
  {
    //swap send & recv
    int y = receive(c2);
    send(c1,1);
    dprint;
  }


/*
 void main()
{
  Channel c1 = open () 
}

*/
