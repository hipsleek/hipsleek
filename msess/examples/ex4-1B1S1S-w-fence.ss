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
     F(S);
     S->H: int;
     S->H: D(B->S: Addr; S->B:Date);
  \/ B->S: 0;).

/* buyer - seller - shipper with fences */
pred_prot GF<B,S,H> ==
  B->S: int;
  S->B: double;
  (  B->S: 1;
     B->S: F-(id,S);
     S->H: F+(id,S);
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


void buyer(Channel c, int id, Double budget, Addr a)
  requires  Chan(c,GF@BS<>)
  ensures   Chan(c,emp)
{ // Chan(c,GF@BS())
  // Chan(c,!int;;?msg:double;;(!1;;!Addr;;?Date or !0));
  send(c, id);
  // Chan(c,?msg:double;;(!1;;!Addr;;?Date or !0));
  Double price = receive(c);
  // Chan(c,(!1;;!Addr;;?Date or !0));
  if(price <= budget) {
    // Chan(c,!1;;!Addr;;?Date or !0);
    send(c, 1);
    // Chan(c,!Addr;;?Date);
    send(c, a);
    // Chan(c,?Date);
    Date sd = receive(c);
    // Chan(c,emp);
  } else
    // Chan(c,!0);
    send(c, 0);
    // Chan(c,emp);
 // Chan(c,emp) & price <= budget \/ Chan(c,emp) & not(price <= budget);
}
/*
 c!1;;c!Addr;;c?Date or c!0
 <==>
 c!x;; case x=1 -> c!Addr;;c?Date
            x=0 -> emp
            else => false

*/


void seller(Channel cb, Channel cs)
  requires Chan(cb, ?int;;!msg:double;;(?1;;?Addr;;!Date or ?0)) *
           Chan(cs, !int;!Chan(b,!Addr;?Date);?(Chan(b,emp)))
  ensures  Chan(cb, emp) * Chan(cs,emp)
{
  /* Chan(cb, ?int;;!msg:double;;(?1;;?Addr;;!Date or ?0)) * */
  /*          Chan(cs, !int;!Chan(b,!Addr;?Date);?(Chan(b,emp))) */
  int id = receive(cb);
  /* Chan(cb, !msg:double;;(?1;;?Addr;;!Date or ?0)) * */
  /*          Chan(cs, !int;!Chan(b,!Addr;?Date);?(Chan(b,emp))) */
  send(cb; getPrice(id));
  /* Chan(cb, (?1;;?Addr;;!Date or ?0)) *
            Chan(cs, !int;!Chan(b,!Addr;?Date);?(Chan(b,emp))) */
  int ans = receive(cb);
  /* Chan(cb, (?Addr;;!Date)) * Chan(cs, !int;!Chan(b,!Addr;?Date);?(Chan(b,emp))) & ans=1 \/
     Chan(cb, (emp) * Chan(cs, !int;!Chan(b,!Addr;?Date);?(Chan(b,emp))) & ans=0 \/
*/
  if(ans == 1){
    Prod p = getProd(id);
    send(cs; p);
    send(cs; cb);
    cb = receive(cs);
  } else if(usr opt == 0)
    return;
  else assert false;
}

// projection of G on H
pred G@H<a> ==
  a?int;a?(Chan(b,ms) * Sess(ms,b?Addr;b!Date));a!(Chan(b,ms) * Sess(ms,emp));

/* should the shipper listen for sellers in a loop? */
void shipper(Channel c)
  requires c::Chan<ms> * ms::Sess{G@H<c>}<>
  ensures  c::Chan<ms> * ms::Sess{emp}<>;
{
  // c::Chan<ms> * ms::Sess{G@H<c>}<>
  // c::Chan<ms> * ms::Sess{c?int;c?(Chan(b,ms) * Sess(ms,b?Addr;b!Date));c!(Chan(b,ms) * Sess(ms,emp));}<>
  Prod p = receive(c);
  // c::Chan<ms> * ms::Sess{c?(Chan(b,ms) * Sess(ms,b?Addr;b!Date));c!(Chan(b,ms) * Sess(ms,emp));}<>
  Channel cd = receive(c);
  // c::Chan<ms> * cd::Chan<ms'> * ms::Sess{c!(Chan(b,ms) * Sess(ms,emp))}<> * ms'::Sess{cd?Addr;cd!Date}<>
  Addr a = receive(cd);
  // c::Chan<ms> * cd::Chan<ms'> * ms::Sess{c!(Chan(b,ms) * Sess(ms,emp))}<> * ms'::Sess{cd!Date}<>
  Date sd = cShip(a; p);
  send(cd; sd);
  // c::Chan<ms> * cd::Chan<ms'> * ms::Sess{c!(Chan(b,ms) * Sess(ms,emp))}<> * ms'::Sess{emp}<>
  send(c; cd);
  // c::Chan<ms> * ms::Sess{c!(Chan(b,ms) * Sess(ms,emp))}<>
}




  Problem A: how to handle or on lhs coming from prot
  Problem B: how to add back the post of send? (Problem with deleg)


cb::Chan<ms> * cs::Chan<ms> * ms::Sess{cs!(Chan(cb,ms) * Sess(ms,cb?Addr;cb!Date));cb?Addr;cb!Date}<>
|-
cs::Chan<ms'> * ms'::Sees<cs!L(msg);rest> * L(msg)


cb::Chan<ms> * cs::Chan<ms> * ms::Sess{cs!(Chan(cb,ms) * Sess(ms,cb?Addr;cb!Date));cb?Addr;cb!Date}<> & ms=ms'
|-
 ms'::Sees<cs!L(msg);rest> * L(msg)

 2. identify L(msg) == (Chan(cb,ms) * Sess(ms,cb?Addr;cb!Date))
 3. identify rest   == cb?Addr;cb!Date

 c::Chan(!msg=0) & x=1 & L=(msg=0)|- c::Chan(!msg.L;P)*L & x=msg.
----------------------------------------------------------------------------------
c::Chan(!msg=1;;!Addr;;?Date;p) & x=1 & L1=(msg=1) & P1=p |- (msg=1) & x=msg.

c::Chan(!msg=1;;!Addr;;?Date;p) & x=1 & L1=(msg=1) & P1=p |- L1 & x=msg.

c::Chan(!msg=1;;!Addr;;?Date;p) & x=1 & L1=(msg=1) & P1=p |- c::Chan(!msg.L1;P1)*L1 & x=msg.

----------------------------------------------------------------------------------
c::Chan(!msg=1;;!Addr;;?Date;P or !msg=0;P) & x=1 |- c::Chan(!msg.L;P)*L & x=msg.


L=!1 & P=!Addr;;?Date;;p & x=1 |- exists msg: (L & x=msg).
L=!1 & P=!Addr;;?Date;;p & x=1 |- exists msg: (msg=1 & x=msg).

L=!0 & P=p & x=1 |- exists msg: (msg=0 & x=msg).

----------------------------------------------------------------------------------
----------------------------------------------------------------------------------
===================================== SEND =======================================
----------------------------------------------------------------------------------

SAT(x=1 & L1=(msg=0) & P1=emp & L1 & x=msg). NO
x=1 & L1=(msg=0) & P1=emp |- L1 & x=msg.


(B) c::Chan(!msg=0) & x=1 |- c::Chan(!msg.L1;P1)*L1 & x=msg.


SAT(x=1 & L1=(msg=1) & P1=!Addr;;?Date;;P & L1 & x=msg). YES
x=1 & L1=(msg=1) & P1=!Addr;;?Date;;P|- L1 & x=msg.


(A) c::Chan(!msg=1;;!Addr;;?Date;p) & x=1 |- c::Chan(!msg.L1;P1)*L1 & x=msg.
----------------------------------------------------------------------------------
c::Chan(!msg=1;;!Addr;;?Date;p or !msg=0;p) & x=1 |- c::Chan(!msg.L1;P1)*L1 & x=msg.


----------------------------------------------------------------------------------
----------------------------------------------------------------------------------
==================================== RECEIVE =====================================
----------------------------------------------------------------------------------

L1=(msg=0) & P1=emp |- emp.                                OK

(B) c::Chan(!msg=0)  |- c::Chan(!msg.L1;;P1).

L1=(msg=1) & P1=!Addr;;?Date;;p |- emp.                    OK

(A) c::Chan(!msg=1;;!Addr;;?Date;;p)  |- c::Chan(!msg.L1;;P1). 

c::Chan(!msg=1;;!Addr;;?Date;;p or !msg=0;;p) & x=1 |- c::Chan(!msg.L1;;P1).



