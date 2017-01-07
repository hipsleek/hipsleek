hip_include 'msess/notes/node.ss'
hip_include 'msess/notes/hodef.ss'
hip_include 'msess/notes/commprimitives.ss'
hip_include 'msess/notes/cdl.ss'

/************* GLOBAL VIEW: **************/
/*********  where ;; is ;{_RS}  ***********/
/*****************************************/
/* pred_sess_prot G<A,B,C> == (A->B:1 * A->C:1);;B->C:2;   */
/* pred_sess_prot G<A,B,C> == (A->B:1 * A->C:1);;CDL(10);;B->C:2;   */
/* pred_sess_prot Gd<A,B,C,c> == ((A->B:1;;[A,B]:downd<c,10>) * (A->C:1;;[A,C]:downd<c,10>));;[C,B]:await<c,10>;;B->C:2; */
pred_sess_prot Gd<A,B,C,c> ==
  ((A->B:1;;[A,B]:downv<c,1,20>) * (A->C:1;;[A,C]:downd<c,10>))
  ;;[C,B]:await<c,10>
  ;;[C,B]:await<c,20>
  ;;B->C:2;



void B(Channel a, Channel b, CDL c)
  requires a::Chan{@S Gd<A@sec,B@prim,C,c>}<> * b::Chan{@S Gd<A,B@prim,C@sec,c>}<> * c::CNT<0,10>
  ensures  a::Chan{emp}<> * b::Chan{emp}<> * c::CNT<(-1),10> * c::CNT<(-1),_>;
{
  int x = receive(a);
  dprint;
  AWAIT(c);
  dprint;
  send(b,2);
}


/* void C(Channel a, Channel b, CDL c, CDL d) */
/*   requires a::Chan{@S Gd<A@sec,B@prim,C,c>}<> * b::Chan{@S Gd<A,B@prim,C@sec,c>}<> * c::CNT<0,10> * d::CNT<0,30> */
/*   ensures  a::Chan{emp}<> * b::Chan{emp}<> * c::CNT<(-1),10>; */
/* { */
/*   int x = receive(a); */
/*   AWAIT(c); */
/*   send(b,2); */
/*   AWAIT(d); */
/*   send(b,3) */
/* } */
