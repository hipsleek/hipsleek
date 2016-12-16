hip_include 'msess/notes/node.ss'
hip_include 'msess/notes/hodef.ss'
hip_include 'msess/notes/commprimitives.ss'
hip_include 'msess/notes/fences.ss'

/************* GLOBAL VIEW: **************/
/* pred_sess_prot G<A,B,C> == A->B:1 * D->B:1;;B->C:1;  */
/* pred_sess_prot G<A,B,C> == A->B:1 * D->B:1;;F(id);;B->C:1;  */
/* pred_sess_prot G<A,B,C> == ((A->B:1;;Fp(id,1/2)) * (D->B:1;;Fp(id,1/2)));;F(id,1);;B->C:1;  */
/* pred_sess_prot G<A,B,C> == ((A->B:1;;Fp2(id,1/2,qqq)) * (D->B:1;;Fp2(id,1/2,qqq)));;Ff(id,qqq);;B->C:1;  */

/************* LOCAL VIEW: **************/
pred_sess_tpproj GBA<> == ?1;;Fa2<22,0.5,qqq>;
pred_sess_tpproj GBC<> == Fc2<22,1.0,qqq> ;; !1;
pred_sess_tpproj GBD<> == ?1;;Fa2<22,0.5,qqq>;
pred_sess_tpproj GAB<> == !1;
pred_sess_tpproj GCB<> == ?1;
pred_sess_tpproj GDB<> == !1;



//should succeed
void B(Channel a, Channel d, Channel c)
  requires a::Chan{@S ?1;;Fa2<22,0.5,qqq>}<> * d::Chan{@S ?1;;Fa2<22,0.5,qqq>}<> * c::Chan{@S Fc2<22,1.0,qqq>;;!1}<>
  ensures  a::Chan{emp}<> * d::Chan{emp}<> * c::Chan{emp}<>;
{
  int x = receive(a);
  int z = receive(d);
  send(c,1);
}

//should succeed
/* void B_P(Channel a, Channel d, Channel c) */
/*   requires a::Chan{@S GBA<>}<> * d::Chan{@S GBD<>}<> * c::Chan{@S GBC<>}<> */
/*   ensures  a::Chan{emp}<> * d::Chan{emp}<> * c::Chan{emp}<>; */
/* { */
/*   int x = receive(a); */
/*   dprint; */
/*   int z = receive(d); */
/*   dprint; */
/*   int y = receive(c); */
/* } */


//should fail
void B_F1(Channel a, Channel d, Channel c)
  requires a::Chan{@S ?1;;Fa2<22,0.5,qqq>}<> * d::Chan{@S ?1;;Fa2<22,0.4,qqq>}<> * c::Chan{@S Fc2<22,0.5,qqq>;;!1}<>
  ensures  a::Chan{emp}<> * d::Chan{emp}<> * c::Chan{emp}<>;
{
  int x = receive(a);
  int z = receive(d);
  send(c,1);
}


//should fail
void B_F2(Channel a, Channel d, Channel c)
  requires a::Chan{@S ?1;;Fa2<22,0.5,qqq>}<> * d::Chan{@S ?1;;Fa2<22,0.4,qqq>}<> * c::Chan{@S Fc2<22,0.9,qqq>;;!1}<>
  ensures  a::Chan{emp}<> * d::Chan{emp}<> * c::Chan{emp}<>;
{
  int x = receive(a);
  int z = receive(d);
  send(c,1);
}


//should fail
void B_F3(Channel a, Channel d, Channel c)
  requires a::Chan{@S ?1;;Fa2<22,0.5,qqq>}<> * d::Chan{@S ?1;;Fa2<22,0.5,qqq>}<> * c::Chan{@S Fc2<22,1.0,qqq>;;!1}<>
  ensures  a::Chan{emp}<> * d::Chan{emp}<> * c::Chan{emp}<>;
{
  int x = receive(a);
  //swapped below two:
  int y = receive(c);
  send(c,1);
}
