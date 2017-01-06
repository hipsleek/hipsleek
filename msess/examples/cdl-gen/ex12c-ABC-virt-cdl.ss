hip_include 'msess/notes/node.ss'
hip_include 'msess/notes/hodef.ss'
hip_include 'msess/notes/commprimitives.ss'
/* hip_include 'msess/notes/cdl.ss' */

data CDL{}

pred_prim CNT<n:int>;
pred_prim downd<c:CDL>;       /* used by the dynamic sync */
pred_prim downv<c:CDL,n:int>; /* used by virt sync: n is used for the initialization of the latch */
pred_prim await<c:CDL>;       /* used by both dyn and virt sync */

void AWAIT(CDL c)
  requires c::CNT<0>
  ensures  c::CNT<(-1)>;
  requires c::CNT<(-1)>
  ensures  c::CNT<(-1)>;

void DOWN(CDL c)
  requires c::CNT<n> & n>0
  ensures  c::CNT<n-1>;

/* ******************* normalization lemmas ******************* */
lemma_norm   "ACC"  self::CNT<n> * self::CNT<m> & m>=0 & n>=0-> self::CNT<m+n>.
lemma_norm   "REL1" self::Chan{@S downd<cc>;;%R}<> -> self::Chan{@S %R}<> * cc::CNT<1>.
lemma_norm@2 "REL2" self::Chan{@S downv<cc,n>;;%R}<> -> self::Chan{@S %R}<> * cc::CNT<n-1>.
lemma_norm   "REL3" self::Chan{@S downv<cc,n>;;%R}<> * cc::CNT<pp>& pp<n -> self::Chan{@S %R}<> * cc::CNT<pp-1>.
lemma_norm   "REL4" self::Chan{@S await<cc>;;%R}<> * cc::CNT<n> & (n=0|n=(0-1)) -> self::Chan{@S %R}<> * cc::CNT<(-1)>.


/* ******************* verification lemmas ******************* */
/* lemma "split" self::CNT<n> & a>=0 & b>=0 & n=a+b -> self::CNT<a> * self::CNT<b>; */
/* lemma "combine" self::CNT<a> * self::CNT<b> & a,b>=0 -> self::CNT<a+b>; */


/************* GLOBAL VIEW: **************/
/* pred_sess_prot G<A,B,C> == A->B:1;;B->C:1;  */
/* pred_sess_prot G<A,B,C> == A->B:1;;CDL(id);;B->C:1; */
/* pred_sess_prot G<A,B,C> == A->B:1;;[A,B]:down(id);;[C,B]:await(id);;B->C:1;  */

/************* LOCAL VIEW: **************/
/*  A@B: !1   */
/*  B@A: ?1;down(id)   */
/*  B@C: await(id);!1  */
/*  C@B:?1  */


void B_dyn(Channel a, Channel b, CDL c)
requires a::Chan{@S ?1;;downd<c>}<> * b::Chan{@S await<c>;;!1}<>  //* c::CNT<1>
  ensures  a::Chan{emp}<> * b::Chan{emp}<> * c::CNT<(-1)>;
{
  int x = receive(a);
  DOWN(c);
  AWAIT(c);
  send(b,1);
}

void B1(Channel a, Channel b)
  requires a::Chan{@S ?1;;downv<c,1>}<> * b::Chan{@S await<c>;;!1}<>  //* c::CNT<1>
  ensures  a::Chan{emp}<> * b::Chan{emp}<> * c::CNT<(-1)>;
{
  int x = receive(a);
  send(b,1);
}


