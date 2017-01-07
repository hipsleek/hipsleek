hip_include 'msess/notes/node.ss'
hip_include 'msess/notes/hodef.ss'
hip_include 'msess/notes/commprimitives.ss'
hip_include 'msess/notes/cdl.ss'

/************* GLOBAL VIEW: **************/
/* pred_sess_prot G<A,B,C,D> == (A->B:1 * C->B:1);;B->D:2;   */
/* pred_sess_prot G<A,B,C,D> == (A->B:1 * C->B:1);;CDL(10);;B->D:2;   */
pred_sess_prot Gv<A,B,C,D,c> == ((A->B:1;;[A,B]:downv<c,2,10>) * (C->B:1;;[C,B]:downv<c,2,10>));;[D,B]:await<c,10>;;B->D:2;


void B1(Channel a, Channel b, Channel c)
  /* requires a::Chan{@S ?1;;downv<c,1,10>}<> * b::Chan{@S await<c,10>;;!1}<>  */
  /* ensures  a::Chan{emp}<> * b::Chan{emp}<>; */
  requires a::Chan{@S Gv<A@sec,B@prim,C,D,c>}<> * b::Chan{@S Gv<A,B@prim,C@sec,D,c>}<> * c::Chan{@S Gv<A,B@prim,C,D@sec,c>}<>
  ensures  a::Chan{emp}<> * b::Chan{emp}<> * c::Chan{emp}<>;
{
  int x = receive(a);
  int y = receive(b);
  send(c,x+y);
}

void B2(Channel a, Channel b, Channel c)
  /* requires a::Chan{@S ?1;;downv<c,1,10>}<> * b::Chan{@S await<c,10>;;!1}<>  */
  /* ensures  a::Chan{emp}<> * b::Chan{emp}<>; */
  requires a::Chan{@S Gv<A@sec,B@prim,C,D,c>}<> * b::Chan{@S Gv<A,B@prim,C@sec,D,c>}<> * c::Chan{@S Gv<A,B@prim,C,D@sec,c>}<>
  ensures  a::Chan{emp}<> * b::Chan{emp}<> * c::Chan{emp}<>;
{
  int y = receive(b);
  int x = receive(a);
  send(c,x+y);
}

/* should fail */
void B3(Channel a, Channel b, Channel c)
  /* requires a::Chan{@S ?1;;downv<c,1,10>}<> * b::Chan{@S await<c,10>;;!1}<>  */
  /* ensures  a::Chan{emp}<> * b::Chan{emp}<>; */
  requires a::Chan{@S Gv<A@sec,B@prim,C,D,c>}<> * b::Chan{@S Gv<A,B@prim,C@sec,D,c>}<> * c::Chan{@S Gv<A,B@prim,C,D@sec,c>}<>
  ensures  a::Chan{emp}<> * b::Chan{emp}<> * c::Chan{emp}<>;
{
  int y = receive(b);
  send(c,2);
  int x = receive(a);
  
}
