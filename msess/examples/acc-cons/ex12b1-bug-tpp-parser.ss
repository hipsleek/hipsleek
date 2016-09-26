hip_include 'msess/notes/node.ss'
hip_include 'msess/notes/hodef.ss'
hip_include 'msess/notes/commprimitives.ss'


pred_prim Fc<id:int,p>; //consumer
pred_prim Fa<id:int,p>; //accumulator

pred_prim Fc2<id:int,p,var>; //consumer
pred_prim Fa2<id:int,p,var>; //accumulator


lemma_norm "ACC"  self::Fa<id,aa> * self::Fa<id,bb> -> self::Fa<id,aa+bb>.
lemma_norm "FULL" self::Fa<id,aaa> & aaa=1 -> self::Fc<id,1>.
lemma_norm "REL"  self::Chan{@S Fa2<id,ppp,qq>;;%R}<> -> self::Chan{@S %R}<> * qq::Fa<id,ppp>.
lemma_norm "CON"  self::Chan{@S Fc2<id,ppp1,qq> ;; %R}<> * qq::Fc<id,ppp2> -> self::Chan{@S %R}<> * qq::Fc<id,ppp2-ppp1>.
lemma_norm "REM"  self::Fc<_,aaa> & aaa=0 -> emp.

/* pred_sess_prot G<A,B,C> == A->B:1 * D->B:1;;C->B:1;  */
/* pred_sess_prot G<A,B,C> == A->B:1 * D->B:1;;F(id);;C->B:1;  */
/* pred_sess_prot G<A,B,C> == ((A->B:1;;Fp(id,1/2)) * (D->B:1;;Fp(id,1/2)));;F(id,1);;C->B:1;  */
/* pred_sess_prot G<A,B,C> == ((A->B:1;;Fp2(id,1/2,qqq)) * (D->B:1;;Fp2(id,1/2,qqq)));;Ff(id,qqq);;C->B:1;  */

pred_sess_proj GBA<> == ?1;;Fa2<22,0.5,qqq>;
pred_sess_proj GBC<> == Fc2<22,1.0,qqq> ;; ?1;
pred_sess_proj GBD<> == ?1;;Fa2<22,0.5,qqq>;
pred_sess_proj GAB<> == !1;
pred_sess_proj GCB<> == !1;
pred_sess_proj GDB<> == !1;


//should succeed
void B_P(Channel a, Channel d, Channel c)
  requires a::Chan{@S GBA<>}<> * d::Chan{@S GBD<>}<> * c::Chan{@S GBC<>}<>
  ensures  a::Chan{emp}<> * d::Chan{emp}<> * c::Chan{emp}<>;
{
  int x = receive(a);
  dprint;
  int z = receive(d);
  dprint;
  int y = receive(c);
}


