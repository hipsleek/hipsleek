hip_include 'msess/notes/node.ss'
hip_include 'msess/notes/hodef.ss'
hip_include 'msess/notes/commprimitives.ss'
hip_include 'msess/notes/fences.ss'

/************* GLOBAL VIEW: **************/
/* pred_sess_prot G<A,B,C,D,E> == (A->B:1 * D->B:1) ;; (B->C:2 * B->E:2);  */
/* pred_sess_prot G<A,B,C,D,E> == (A->B:1 * D->B:1) ;; F(id) ;; (B->C:1 * B->E:2);  */
/* pred_sess_prot G<A,B,C,D,E> == ((A->B:1;;Fa(id,1/2)) * (D->B:1;;Fa(id,1/2))) ;; ((Fc(id,1/2);;B->C:1) * (Fc(id,1/2);;B->E:2)) ;  */
/* pred_sess_prot G<A,B,C,D,E> == ((A->B:1;;Fa2(id,1/2,qqq)) * (D->B:1;;Fa2(id,1/2,qqq))) ;; ((Fc(id,1/2,qqq);;B->C:1) * (Fc(id,1/2,qqq);;B->E:2));  */

/************* LOCAL VIEW: **************/
pred_sess_tpproj GBA<> == ?1;;Fa2<22,0.5,qqq>;
pred_sess_tpproj GBC<> == Fc2<22,1.0,qqq> ;; ?1;
pred_sess_tpproj GBD<> == ?1;;Fa2<22,0.5,qqq>;
pred_sess_tpproj GAB<> == !1;
pred_sess_tpproj GCB<> == !1;
pred_sess_tpproj GDB<> == !1;

//should succeed
  void B(Channel a, Channel d, Channel c, Channel e)
  requires a::Chan{@S ?1;;Fa2<22,0.5,qqq>}<> * d::Chan{@S ?1;;Fa2<22,0.5,qqq>}<> * c::Chan{@S Fc2<22,0.5,qqq>;;!1}<> * e::Chan{@S Fc2<22,0.5,qqq>;;!2}<>
  ensures  a::Chan{emp}<> * d::Chan{emp}<> * c::Chan{emp}<> * e::Chan{emp}<>;
{
  int x = receive(a);
  int z = receive(d);
  
  send(c,1);
  send(e,2);
}


//should fail
  void B_F1(Channel a, Channel d, Channel c, Channel e)
  requires a::Chan{@S ?1;;Fa2<22,0.5,qqq>}<> * d::Chan{@S ?1;;Fa2<22,0.4,qqq>}<> * c::Chan{@S Fc2<22,0.5,qqq>;;!1}<> * e::Chan{@S Fc2<22,0.4,qqq>;;!2}<>
  ensures  a::Chan{emp}<> * d::Chan{emp}<> * c::Chan{emp}<> * e::Chan{emp}<>;
{
  int x = receive(a);
  int z = receive(d);
  send(c,1);
  send(e,2);
}


//should succeed
  void B_F2(Channel a, Channel d, Channel c, Channel e)
  requires a::Chan{@S ?1;;Fa2<22,0.5,qqq>}<> * d::Chan{@S ?1;;Fa2<22,0.5,qqq>}<> * c::Chan{@S Fc2<22,0.5,qqq>;;!1}<> * e::Chan{@S Fc2<22,0.5,qqq>;;!2}<>
  ensures  a::Chan{emp}<> * d::Chan{emp}<> * c::Chan{emp}<> * e::Chan{emp}<>;
{
  int x = receive(a);
  int z = receive(d);
  //swapped below two:
  send(e,2);
  send(c,1);

}


//should succeed
  void B_F3(Channel a, Channel d, Channel c, Channel e)
  requires a::Chan{@S ?1;;Fa2<22,0.5,qqq>}<> * d::Chan{@S ?1;;Fa2<22,0.5,qqq>}<> * c::Chan{@S Fc2<22,0.5,qqq>;;!1}<> * e::Chan{@S Fc2<22,0.5,qqq>;;!2}<>
  ensures  a::Chan{emp}<> * d::Chan{emp}<> * c::Chan{emp}<> * e::Chan{emp}<>;
{
  //swapped below two:
  int z = receive(d);
  int x = receive(a);
  send(c,1);
  send(e,2);
}
