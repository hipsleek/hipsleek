hip_include 'msess/notes/node.ss'
hip_include 'msess/notes/hodef.ss'
hip_include 'msess/notes/commprimitives.ss'
hip_include 'msess/notes/fences.ss'

/************* GLOBAL VIEW: **************/
/* pred_sess_prot G<A,B,C> == A->B:1;;B->C:1;  */
/* pred_sess_prot G<A,B,C> == A->B:1;;F(id);;B->C:1; */
/* pred_sess_prot G<A,B,C> == A->B:1;;Fa(id,1);;Fc(id,1);;B->C:1;  */

/************* LOCAL VIEW: **************/
pred_sess_tpproj GBA<> == ?1;;Fp2<22,1,qqq>;
pred_sess_tpproj GAB<> == !1;

pred_sess_tpproj GBC<> == Fm2<22,1,qqq,1>;;!1;
pred_sess_tpproj GCB<> == ?1;


void B(Channel a, Channel c)
  requires a::Chan{@S ?1;;Fp2<22,1,qqq>}<> * c::Chan{@S Fm2<22,1,qqq,1>;;!1}<> 
  /* requires a::Chan{@S ?1;;Fp<22,1>}<> * c::Chan{@S Fp<22,1>;;?1}<> */
  /* requires a::Chan{@S ?1}<> * c::Chan{@S !1}<> */
  ensures  a::Chan{emp}<> * c::Chan{emp}<>;
{
  dprint;
  int x = receive(a); 
  dprint;
  send(c,1);
}
