hip_include 'msess/notes/node.ss'
hip_include 'msess/notes/hodef.ss'
hip_include 'msess/notes/commprimitives.ss'


pred_prim Ff<id:int>; //full
pred_prim Fp<id:int,p>; //partial

pred_prim Ff2<id:int,var>; //full
pred_prim Fp2<id:int,p,var>; //partial

/* lemma_norm "ACC" self::Fp<id,a> * self::Fp<id,b> -> self::Fp<id,a+b>; */
/* lemma_norm "FULL" self::Fp<id,p> & p=0 -> self::Ff<id>; */
/* lemma_norm "REL" self::Chan{@S Fp<id,a>;;%R}<> -> self::Chan{@S %R}<> * self::Fp<id,a>; */
/* lemma "SYNC-CHECK" self::Chan{@S Ff<id> ;; %R}<> * self::Ff<id> -> self::Chan{@S %R}<> * self::Ff<id>; */

/* ll  = self::node<> or */
/*   ...ll<> */
  
/* sll = self::node<> or */
/*   ... sll<> */

/*   lemma  self::sll<n> -> self::ll<n> */

lemma_norm "ACC" self::Fp<id,aa> * self::Fp<id,bb> -> self::Fp<id,aa+bb>.
/* lemma_prop  "ACC2" self::Fp<id,aa> * self::Fp<id,bb> & m=aa+bb -> self::Fp<id,m>. */
lemma_norm "FULL" self::Fp<id,aaa> & aaa=1 -> self::Ff<id>.
lemma_norm "REL2" self::Chan{@S Fp2<id,bbb,q>;;%R}<> -> self::Chan{@S %R}<> * q::Fp<id,bbb>.
lemma_norm "SYNC-CHECK" self::Chan{@S Ff2<id,ppp> ;; %R}<> * ppp::Ff<id> -> self::Chan{@S %R}<> * ppp::Ff<id>.

 pred_sess_prot G<A,B,C> == A->B:1;;C->B:1; 
pred_sess_prot G<A,B,C> == A->B:1;;F(id);;C->B:1;
pred_sess_prot G<A,B,C> == A->B:1;;Fp(id,1);;C->B:1; 

pred_sess_tpproj GBA<> == ?1;
pred_sess_tpproj GBC<> == ?1;
pred_sess_tpproj GAB<> == !1;
pred_sess_tpproj GCB<> == !1;

void B(Channel a, Channel c)
  requires a::Chan{@S ?1;;Fp2<22,1,qqq>}<> * c::Chan{@S Ff2<22,qqq>;;?1}<>
  /* requires a::Chan{@S ?1;;Fp<22,1>}<> * c::Chan{@S Fp<22,1>;;?1}<> */
  /* requires a::Chan{@S ?1}<> * c::Chan{@S ?1}<> */
  ensures  a::Chan{emp}<> * c::Chan{emp}<>;
{
  dprint;
  int x = receive(a); 
  dprint;
  int y = receive(c);
}
