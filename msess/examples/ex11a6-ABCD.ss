hip_include 'msess/notes/node.ss'
hip_include 'msess/notes/hodef.ss'
hip_include 'msess/notes/commprimitives.ss'


//pred_prim Ff<id:int>; //full
pred_prim Ff<id:int>; //full
pred_prim Fp<id:int,part:int>; //partial

pred_prim Ff2<id:int,var>; //full
pred_prim Fp2<id:int,part:int,var>; //partial

lemma_norm "ACC" self::Fp<id,aa> * self::Fp<id,bb> -> self::Fp<id,aa+bb>.
lemma_norm "FULL" self::Fp<id,aaa> & aaa=1 -> self::Ff<id>.
lemma_norm "REL" self::Chan{@S Fp2<id,ppp,q>;;%R}<> -> self::Chan{@S %R}<> * q::Fp<id,ppp>.
lemma_norm "SYNC-CHECK" self::Chan{@S Ff2<id,ppp> ;; %R}<> * ppp::Ff<id> -> self::Chan{@S %R}<> * ppp::Ff<id>.

/* pred_sess_prot G<A,B,C> == A->B:1 * D->B:1;;C->B:1;  */
/* pred_sess_prot G<A,B,C> == A->B:1 * D->B:1;;F(id);;C->B:1;  */
/* pred_sess_prot G<A,B,C> == ((A->B:1;;Fp(id,1/2)) * (D->B:1;;Fp(id,1/2)));;F(id,1);;C->B:1;  */
/* pred_sess_prot G<A,B,C> == ((A->B:1;;Fp2(id,1/2,qqq)) * (D->B:1;;Fp2(id,1/2,qqq)));;Ff(id,qqq);;C->B:1;  */

pred_sess_proj GBA<> == ?1;
pred_sess_proj GBC<> == ?1;
pred_sess_proj GBD<> == ?1;
pred_sess_proj GAB<> == !1;
pred_sess_proj GCB<> == !1;
pred_sess_proj GDB<> == !1;

void B(Channel a, Channel d, Channel c)
  requires a::Chan{@S ?1;;Fp2<22,0.5,qqq>}<> * d::Chan{@S ?1;;Fp2<22,0.5,qqq>}<> * c::Chan{@S Ff2<22,qqq>;;?1}<>
  ensures  a::Chan{emp}<> * d::Chan{emp}<> * c::Chan{emp}<>;
{
  int x = receive(a);
  dprint;
  int z = receive(d);
  dprint;
  int y = receive(c);
}
