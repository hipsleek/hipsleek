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


data cdl {int id;}

pred_prim CDL<id: int>;

pred_sess_prot G<A,B,C,D> == A->B:1;; CDL<22>;;C->D:2;


void B(Channel b, cdl c)
  requires b::Chan{@S ?1}<>
  ensures b::Chan{emp}<>;
{
 int x = receive(b);
}

