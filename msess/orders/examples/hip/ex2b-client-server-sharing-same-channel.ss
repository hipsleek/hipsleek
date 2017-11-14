hip_include 'msess/notes/node.ss'
hip_include 'msess/notes/hodef.ss'
hip_include 'msess/notes/commprimitives.ss'

/* S - server, C - client
   c - shared channel
*/
pred_sess_prot G<S:role,C:role,c:chan> == C->S:c(1) ;; S->C:c(v#v>0);

int foo(int x)
  requires x>0
  ensures  res = x + x;

/*
   c - channels shared between the client & server
*/
//Should FAIL since it needs extra sync instruments
void server(Channel c)
  requires c::Chan{@S G<S@peer,C,c@chan>}<> 
  ensures  c::Chan{@S emp}<>;
  {
    int x = receive(c);
    int y = foo(x);
    send(c,y);
    dprint;
  }

/*
   c - channels shared between the client & server
*/
//Should FAIL since it needs extra sync instruments
void client(Channel c)
  requires c::Chan{@S G<S,C@peer,c@chan>}<> 
  ensures  c::Chan{@S emp}<>;
  {
    send(c,1);
    int y = receive(c);
    dprint;
  }
