hip_include 'msess/notes/node.ss'
hip_include 'msess/notes/hodef.ss'
hip_include 'msess/notes/commprimitives.ss'


//pred_prim Ff<id:int>; //full
pred_prim Ff<id:int,bound:int>; //full
pred_prim Fp<id:int,part:int>; //partial

pred_prim Ff2<id:int,bound:int,var>; //full
pred_prim Fp2<id:int,part:int,var>; //partial

/* lemma_norm "ACC" self::Fp<id,a> * self::Fp<id,b> -> self::Fp<id,a+b>; */
/* lemma_norm "FULL" self::Fp<id,p> & p=0 -> self::Ff<id>; */
/* lemma_norm "REL" self::Chan{@S Fp<id,a>;;%R}<> -> self::Chan{@S %R}<> * self::Fp<id,a>; */
/* lemma "SYNC-CHECK" self::Chan{@S Ff<id> ;; %R}<> * self::Ff<id> -> self::Chan{@S %R}<> * self::Ff<id>; */

lemma_norm "ACC" self::Fp<id,aa> * self::Fp<id,bb> -> self::Fp<id,aa+bb>;
lemma_norm "FULL" self::Fp<id,aaa> & aaa=1 -> self::Ff<id>.
lemma_norm "REL2" self::Chan{@S Fp2<id,bbb,q>;;%R}<> -> self::Chan{@S %R}<> * q::Fp<id,bbb>;
lemma_norm "SYNC-CHECK1" self::Chan{@S Ff2<id,ppp> ;; %R}<> * ppp::Fp<id> -> self::Chan{@S %R}<> * ppp::Ff<id>;
lemma_norm "SYNC-CHECK2" self::Chan{@S Ff2<id,ppp> ;; %R}<> * ppp::Ff<id> -> self::Chan{@S %R}<> * ppp::Ff<id>;

/* pred_sess_prot G<A,B,C> == A->B:1 * D->B:1;;C->B:1;  */
/* pred_sess_prot G<A,B,C> == A->B:1 * D->B:1;;F(id);;C->B:1;  */
/* pred_sess_prot G<A,B,C> == ((A->B:1;;Fp(id,1/2)) * (D->B:1;;Fp(id,1/2)));;F(id,1);;C->B:1;  */
/* pred_sess_prot G<A,B,C> == ((A->B:1;;Fp2(id,1/2,qqq)) * (D->B:1;;Fp2(id,1/2,qqq)));;Ff(id,qqq);;C->B:1;  */


/* pred_sess_prot G<A,B,C> == (A->B:1 * D->B:1);;(C->B:1 * E->B:1);  */
/* pred_sess_prot G<A,B,C> == A->B:1 * D->B:1;;F(id);;(C->B:1 * E->B:1);  */
/* pred_sess_prot G<A,B,C> == ((A->B:1;;Fp(id,1/2)) * (D->B:1;;Fp(id,1/2)));;((F (id,1);; C-> B: 1) * (F (id,1);; E-> B: 1));  */



pred_sess_tpproj GBA<> == ?1;
pred_sess_tpproj GBC<> == ?1;
pred_sess_tpproj GBD<> == ?1;
pred_sess_tpproj GAB<> == !1;
pred_sess_tpproj GCB<> == !1;
pred_sess_tpproj GDB<> == !1;

void B(Changnel a, Channel d, Channel c)
  requires a::Chan{@S ?1;;Fp2<22,2,qqq>}<> * d::Chan{@S ?1;;Fp2<22,2,qqq>}<> * c::Chan{@S Ff2<22,4,qqq>;;?1}<>
  /* requires a::Chan{@S ?1;;Fp<22,1>}<> * c::Chan{@S Fp<22,1>;;?1}<> */
  ensures  a::Chan{emp}<> * d::Chan{emp}<>; //* c::Chan{emp}<>;
{
  int x = receive(a);
  dprint;
  int z = receive(d);
  dprint;
  // int y = receive(c);
}
