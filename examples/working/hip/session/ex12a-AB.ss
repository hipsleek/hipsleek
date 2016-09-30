hip_include 'msess/notes/node.ss'
hip_include 'msess/notes/hodef.ss'
hip_include 'msess/notes/commprimitives.ss'


pred_prim Fc<id:int,p:float>; //consumer
pred_prim Fa<id:int,p:float>; //accumulator

pred_prim Fc2<id:int,p:float,var>; //consumer
pred_prim Fa2<id:int,p:float,var>; //accumulator


lemma_norm "ACC"  self::Fa<id,aa> * self::Fa<id,bb> -> self::Fa<id,aa+bb>.
lemma_norm "FULL" self::Fa<id,aaa> & aaa=1.0 -> self::Fc<id,1.0>.
lemma_norm "REL"  self::Chan{@S Fa2<id,ppp,qq>;;%R}<> -> self::Chan{@S %R}<> * qq::Fa<id,ppp>.
lemma_norm "CON"  self::Chan{@S Fc2<id,ppp1,qq> ;; %R}<> * qq::Fc<id,ppp2> -> self::Chan{@S %R}<> * qq::Fc<id,ppp2-ppp1>.
lemma_norm "REM"  self::Fc<_,aaa> & aaa=0.0 -> emp.


/* pred_sess_prot G<A,B,C> == A->B:1 ;; C->B:1;  */
/* pred_sess_prot G<A,B,C> == A->B:1 ;; F(id) ;; C->B:1; */
/* pred_sess_prot G<A,B,C> == A->B:1;; Fa(id,1.0) ;; Fc(id,1.0) ;; C->B:1;  */

pred_sess_tpproj GBA<> == ?1;
pred_sess_tpproj GBC<> == ?1;
pred_sess_tpproj GAB<> == !1;
pred_sess_tpproj GCB<> == !1;

void B(Channel a, Channel c)
  requires a::Chan{@S ?1;;Fa2<22,1.0,qqq>}<> * c::Chan{@S Fc2<22,1.0,qqq>;;?1}<>
  /* requires a::Chan{@S ?1;;Fp<22,1>}<> * c::Chan{@S Fp<22,1>;;?1}<> */
  /* requires a::Chan{@S ?1}<> * c::Chan{@S ?1}<> */
  ensures  a::Chan{emp}<> * c::Chan{emp}<>;
{
  dprint;
  int x = receive(a); 
  dprint;
  int y = receive(c);
}
