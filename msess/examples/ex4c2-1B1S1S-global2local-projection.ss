hip_include "msses/notes/hodef.ss"
hip_include "msses/notes/commprimitives.ss"
data node {int info; node next;}
gdata Channel{int info;}

pred_prim Sess{%P}<>;
pred_prim Chan<s:Sess>;

/* buyer - seller - shipper */
pred_prot G<B,S,H> ==
  B->S: int;
  S->B: double;
  (  B->S: 1;
     S->H: int;
     S->H: D(B->S: Addr; S->B:Date);
  \/ B->S: 0;).

/* buyer - seller - shipper with fences */
pred_prot GF<B,S,H> ==
  B->S: int;
  S->B: double;
  (  B->S: 1;
     F(S,id);
     S->H: int;
     S->H: D(B->S: Addr; S->B:Date);
  \/ B->S: 0;).

/* buyer - seller - shipper with fences */
pred_prot GF<B,S,H> ==
  B->S: int;
  S->B: double;
  (  B->S: 1;
     B->S: F-(S,id);
     S->H: F+(S,id);
     S->H: int;
     S->H: D(B->S: Addr; S->B:Date);
  \/ B->S: 0;).

/* buyer - seller - shipper with fences */
pred_prot GF<B,S,H> ==
  B->S: int;
  S->B: double;
  (  B->S: 1;
     B->S: F-(S,id);
     S->H: F+(S,id);
     S->H: int;
     S->H: D(B->S: Addr; S->B:Date);
  \/ B->S: 0;).
  
// projection of GF on buyer
//pred_proj GF@BS<bs> == bs!int;;bs?msg:double;;(bs!1;;bs!Addr;;bs?Date or bs!0);
pred_proj GF@BS<> == !int;;?msg:double;;(!1;;!Addr;;?Date or !0);

// projection of GF on seller (wrt buyer)
//pred_proj GF@SB<bs> == ~GF@BS<bs>
pred_proj GF@SB<> == ~GF@BS<>
  == ?int;;!msg:double;;(?1;;@F(c);?Addr;;!Date or ?0);
// projection of G on shipper
//pred GF@HS<a> ==
//  a?int;a?Chan(b,b?Addr;b!Date);a!(Chan(b,emp));
pred GF@HS<> ==
  ?int;?Chan(b,?Addr;!Date);!(Chan(b,emp));

// projection of GF on seller (wrt shipper)
/* pred GF@SH<a> == ~ GF@HS<a> */
pred GF@SH<> == ~ GF@HS<>
  == @F(consume);!int;!Chan(b,!Addr;?Date);?(Chan(b,emp));

