hip_include 'msess/notes/node.ss'
hip_include 'msess/notes/hodef.ss'
hip_include 'msess/notes/commprimitives.ss'
hip_include 'msess/notes/fences.ss'

/************* GLOBAL VIEW: **************/
/* pred_sess_prot G<A,B,C,D,E> == (A->B:1 * D->B:1) ;; (B->C:2 * B->E:2);  */
/* pred_sess_prot G<A,B,C,D,E> == (A->B:1 * D->B:1) ;; F(id) ;; (B->C:1 * B->E:2);  */
/* pred_sess_prot G<A,B,C,D,E> == ((A->B:1;;Fp(id,1)) * (D->B:1;;Fp(id,1))) ;; ((Fm(id,2,1/2);;B->C:1) * (Fc(id,2,1/2);;B->E:2)) ;  */
/* pred_sess_prot G<A,B,C,D,E> == ((A->B:1;;Fp2(id,1,qqq)) * (D->B:1;;Fp2(id,1,qqq))) ;; ((Fm2(id,2,qqq,1/2);;B->C:1) * (Fm2(id,2,qqq,1/2);;B->E:2));  */

/************* LOCAL VIEW: **************/

//should succeed
  void B(Channel a, Channel d, Channel c, Channel e)
requires a::Chan{@S ?1;;Fp2<22,1,qqq>}<> * d::Chan{@S ?1;;Fp2<22,1,qqq>}<> * c::Chan{@S Fm2<22,2,qqq,0.5>;;!1}<> * e::Chan{@S Fm2<22,2,qqq,0.5>;;!2}<>
  ensures  a::Chan{emp}<> * d::Chan{emp}<> * c::Chan{emp}<> * e::Chan{emp}<>;
{
  int x = receive(a);
  int z = receive(d);
  
  send(c,1);
  send(e,2);
}


//should fail
  void B_F1(Channel a, Channel d, Channel c, Channel e)
    requires a::Chan{@S ?1;;Fp2<22,1,qqq>}<> * d::Chan{@S ?1;;Fp2<22,1,qqq>}<> * c::Chan{@S Fm2<22,3,qqq,0.5>;;!1}<> * e::Chan{@S Fm2<22,3,qqq,0.5>;;!2}<>
  ensures  a::Chan{emp}<> * d::Chan{emp}<> * c::Chan{emp}<> * e::Chan{emp}<>;
{
  int x = receive(a);
  int z = receive(d);
  send(c,1);
  send(e,2);
}


//should succeed
  void B_F2(Channel a, Channel d, Channel c, Channel e)
   requires a::Chan{@S ?1;;Fp2<22,1,qqq>}<> * d::Chan{@S ?1;;Fp2<22,1,qqq>}<> * c::Chan{@S Fm2<22,2,qqq,0.5>;;!1}<> * e::Chan{@S Fm2<22,2,qqq,0.5>;;!2}<>
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
    requires a::Chan{@S ?1;;Fp2<22,1,qqq>}<> * d::Chan{@S ?1;;Fp2<22,1,qqq>}<> * c::Chan{@S Fm2<22,2,qqq,0.5>;;!1}<> * e::Chan{@S Fm2<22,2,qqq,0.5>;;!2}<>
  ensures  a::Chan{emp}<> * d::Chan{emp}<> * c::Chan{emp}<> * e::Chan{emp}<>;
{
  //swapped below two:
  int z = receive(d);
  int x = receive(a);
  send(c,1);
  send(e,2);
}
