hip_include 'msess/notes/node.ss'
hip_include 'msess/notes/hodef.ss'
hip_include 'msess/notes/commprimitives.ss'
hip_include 'msess/notes/cdl.ss'


/************* GLOBAL VIEW: **************/
/* pred_sess_prot G<A,B,C> == A->B:1;;B->C:1;  */
/* pred_sess_prot G<A,B,C> == A->B:1;;CDL(id);;B->C:1; */
  pred_sess_prot Gd<A,B,C,c> == A->B:1;;[A,B]:downd<c>;;[C,B]:await<c,_>;;B->C:1;
pred_sess_prot Gv<A,B,C,c> == A->B:1;;[A,B]:downv<c,1,10>;;[C,B]:await<c,10>;;B->C:1;
/************* LOCAL VIEW: **************/
/*  A@B: !1   */
/*  B@A: ?1;down(id)   */
/*  B@C: await(id);!1  */
/*  C@B:?1  */



void B_dyn(Channel a, Channel b, CDL c)
  /* requires a::Chan{@S ?1;;downd<c>}<> * b::Chan{@S await<c>;;!1}<>  //\* c::CNT<1> */
  /* ensures  a::Chan{emp}<> * b::Chan{emp}<> * c::CNT<(-1)>; */
  requires a::Chan{@S Gd<A@sec,B@prim,C,c>}<> * b::Chan{@S Gd<A,B@prim,C@sec,c>}<>  //* c::CNT<1>
  ensures  a::Chan{emp}<> * b::Chan{emp}<> * c::CNT<(-1),_>;
{
  int x = receive(a);
  DOWN(c);
  AWAIT(c);
  send(b,1);
}

void B1(Channel a, Channel b)
  /* requires a::Chan{@S ?1;;downv<c,1,10>}<> * b::Chan{@S await<c,10>;;!1}<>  */
  /* ensures  a::Chan{emp}<> * b::Chan{emp}<>; */
  requires a::Chan{@S Gv<A@sec,B@prim,C,c>}<> * b::Chan{@S Gv<A,B@prim,C@sec,c>}<> 
  ensures  a::Chan{emp}<> * b::Chan{emp}<>;
{
  int x = receive(a);
  send(b,1);
}

/* should fail */
void B2(Channel a, Channel b)
  requires a::Chan{@S ?1;;downv<c,1,10>}<> * b::Chan{@S await<c,20>;;!1}<>  //* c::CNT<1>
  ensures  a::Chan{emp}<> * b::Chan{emp}<>;
{
  int x = receive(a);
  send(b,1);
}


