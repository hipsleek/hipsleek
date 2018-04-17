hip_include 'msess/notes/node.ss'
hip_include 'msess/notes/hodef.ss'
hip_include 'msess/notes/commprimitives.ss'
/* hip_include 'msess/notes/fences.ss' */

/************* GLOBAL VIEW: **************/
/* pred_sess_prot G<A,B,C> == A->B:1;;B->C:1;  */
/* pred_sess_prot G<A,B,C> == A->B:1;;CDL(id);;B->C:1; */
/* pred_sess_prot G<A,B,C> == A->B:1;;[A,B]:down(id);;[C,B]:await(id);;B->C:1;  */

/************* LOCAL VIEW: **************/
/*  A@B: !1   */
/*  B@A: ?1;down(id)   */
/*  B@C: await(id);!1  */
/*  C@B:?1  */

data CDL{}

pred_prim CNT<n:int>;
pred_prim down<id:CDL>;
pred_prim await<id:CDL>;

void AWAIT(CDL c)
  requires c::CNT<0>
  ensures  c::CNT<(-1)>;

void DOWN(CDL c)
  requires c::CNT<n> & n>0
  ensures  c::CNT<n-1>;

lemma_norm "REL" self::Chan{@S down<cc>;;%R}<> -> self::Chan{@S %R}<> * cc::CNT<1>.
lemma_norm "REL" self::Chan{@S await<cc>;;%R}<> * cc::CNT<(-1)> -> self::Chan{@S %R}<> * cc::CNT<(-1)>.

void B1(Channel a, Channel b, CDL c)
  /* requires a::Chan{@S ?1;down(id)}<> * b::Chan{@S await(id);!1}<> * c::CDL<id> * c::CNT<n> */
  /* ensures  a::Chan{emp}<> * b::Chan{emp}<> * c::CDL<id> * c::CNT<-1>; */
  requires a::Chan{@S ?1;;down<c>}<> * b::Chan{@S await<c>;;!1}<>  //* c::CNT<1>
  ensures  a::Chan{emp}<> * b::Chan{emp}<> * c::CNT<(-1)>;
{
  int x = receive(a)[int];
  DOWN(c);
  AWAIT(c);
  send(b,1)[int];
}


/* should FAIL  */
void B2(Channel a, Channel b, CDL c)
  /* requires a::Chan{@S ?1;down(id)}<> * b::Chan{@S await(id);!1}<> * c::CDL<id> * c::CNT<n> */
  /* ensures  a::Chan{emp}<> * b::Chan{emp}<> * c::CDL<id> * c::CNT<-1>; */
  requires a::Chan{@S ?1;;down<c>}<> * b::Chan{@S await<c>;;!1}<>  //* c::CNT<1>
  ensures  a::Chan{emp}<> * b::Chan{emp}<> * c::CNT<(-1)>;
{
  int x = receive(a)[int];
  DOWN(c);
  send(b,1)[int];
  AWAIT(c);
}

/* should FAIL  */
void B3(Channel a, Channel b, CDL c)
  /* requires a::Chan{@S ?1;down(id)}<> * b::Chan{@S await(id);!1}<> * c::CDL<id> * c::CNT<n> */
  /* ensures  a::Chan{emp}<> * b::Chan{emp}<> * c::CDL<id> * c::CNT<-1>; */
  requires a::Chan{@S ?1;;down<c>}<> * b::Chan{@S await<c>;;!1}<>  //* c::CNT<1>
  ensures  a::Chan{emp}<> * b::Chan{emp}<> * c::CNT<(-1)>;
{
  DOWN(c);
  int x = receive(a)[int];
  AWAIT(c);
  send(b,1)[int];
}
