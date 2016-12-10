hip_include 'msess/notes/node.ss'
hip_include 'msess/notes/hodef.ss'
hip_include 'msess/notes/fences.ss'
hip_include 'msess/notes/commprimitives.ss'


//CountDownLatch
/* data CDL {} */

/* data cell { int val; } */

/* pred_prim LatchIn{-%P@Split}<>; */

/* pred_prim LatchOut{+%P@Split}<>; */

/* pred_prim CNT<n:int> */
/*   inv n>=(-1); */

/* lemma "split" self::CNT<n> & a>=0 & b>=0 & n=a+b -> self::CNT<a> * self::CNT<b>; */

/* lemma "combine" self::CNT<a> * self::CNT<b> & a,b>=0 -> self::CNT<a+b>; */

/* /\********************************************\/ */
/* CDL create_latch(int n) with %P */
/*   requires n>0 */
/*   ensures res::LatchIn{-%P}<> * res::LatchOut{+%P}<> * res::CNT<n>; */
/*   requires n=0 */
/*   ensures res::CNT<(-1)>; */

/* void countDown(CDL c) */
/*   requires c::LatchIn{-%P}<> * %P * c::CNT<n> & n>0 */
/*   ensures c::CNT<n-1>; */
/*   requires c::CNT<(-1)>  */
/*   ensures c::CNT<(-1)>; */

/* void await(CDL c) */
/*   requires c::LatchOut{+%P}<> * c::CNT<0> */
/*   ensures c::CNT<(-1)> * %P; */
/*   requires c::CNT<(-1)> */
/*   ensures c::CNT<(-1)>; */

/* pred_sess_prot G1<A,B,C,D> == A->B:1 ;; C->D:2; */

pred_prim CNT<n:int>
  inv n>=(-1);

data cdl {int id;}

pred_prim ghost<id: int>;
pred_prim CDL{%P}<id: int>;
pred_prim GA<id: int>;
pred_prim GC<id: int,ptr>;

void countDown(cdl c)
  requires c::CDL{%P}<id> * %P * c::CNT<n> & n>0
  ensures c::CNT<n-1>;
  /* requires c::CNT<(-1)> */
  /* ensures c::CNT<(-1)>; */

void await(cdl c)
  requires c::CDL{%P}<id> * c::CNT<0>
  ensures c::CNT<(-1)> * %P;
/*   requires c::CNT<(-1)> */
/*   ensures c::CNT<(-1)>; */


//pred_sess_prot G<A,B,C,D> == A->B:1;; CDL<_>;;C->D:2;

/* lemma_norm "ACC"  self::Fa<id,aa> * self::Fa<id,bb> & aa+bb<=1.0-> self::Fa<id,aa+bb>. */
/* lemma_norm "FULL" self::Fa<id,aaa> & aaa=1.0 -> self::Fc<id,1.0>. */
/* lemma_norm "REL"  self::Chan{@S Fa2<id,ppp,qq>;;%R}<> -> self::Chan{@S %R}<> * qq::Fa<id,ppp>. */
/* lemma_norm "CON"  self::Chan{@S Fc2<id,ppp1,qq> ;; %R}<> * qq::Fc<id,ppp2> & ppp2>=ppp1 -> self::Chan{@S %R}<> * qq::Fc<id,ppp2-ppp1>. */
/* lemma_norm "REM"  self::Fc<id,aaa> & aaa=0.0 -> emp. */

lemma_norm "RELCDL"  self::Chan{@S GA<id>;;%R}<> -> self::Chan{@S %R}<> * self::GA<id>.
lemma_norm "CONCDL"  self::Chan{@S GC<id,ptr>;;%R}<> * ptr::GC<id,ptr> -> self::Chan{@S %R}<>. 
                                                 /*
void B(Channel b, cdl c)
  requires b::Chan{@S ?1;;GA<id>}<> * c::CDL{ b::GA<id>}<id> * c::CNT<1>
  ensures b::Chan{emp}<>;
{
 int x = receive(b);
 // b::Chan{@S GR<id>} * c::CDL{ b::GR<id>}<id>
 dprint;
 countDown(c);
}
*/
void C(Channel b, cdl c)
  requires b::Chan{@S GC<id,b>;;!2}<> * c::CDL{ b::GC<id,b>}<id> * c::CNT<0>
  ensures b::Chan{emp}<>;
{
 await(c);
 // b::Chan{@S GR<id>} * c::CDL{ b::GR<id>}<id>
 dprint;
 send(b,2);
}


/*
why below is right?

============
RIGHT LEMMAS
============
[Lemma "CONCDL":  self::Chan{ . HVar R[]&{FLOW,(4,5)=__norm#E}}<>@M&{FLOW,(4,5)=__norm#E}<== (exists id_2278,
ptr_2279: self::Chan{ . (GC{}<[id_2278,ptr_2279]>) ;; (%R)
&{FLOW,(4,5)=__norm#E}}<>@M * 
          ptr_2279::GC<id_2278,ptr_2279>@M&
{FLOW,(4,5)=__norm#E})]

*/
