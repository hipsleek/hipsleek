hip_include "msses/notes/hodef.ss"
hip_include "msses/notes/commprimitives.ss"
data node {int info; node next;}
data Channel{int info;}

pred_prim Sess{%P}<>;
pred_prim Chan<s:Sess>;

/* buyer - seller - shipper */
pred_prot G<B,S,H> ==
  B->S: int;    //prod id
  S->B: double; //price
  (  B->S: 1;
     S->H: int    //prod id
     S->H: D(B->S: Addr; S->B:Date); //delegating to H the role of S
  \/ B->S: 0;).


// projection of G on B:
pred_proj G@B<bs> == bs!int;;bs?msg:double;;(bs!1;;bs!Addr;;bs?Date or bs!0);

void buyer(Channel c, int id, Double budget, Addr a)
  requires  c::Chan<ms> * ms::Sess{G@B<c>}<>
  ensures   c::Chan<ms> * ms::Sess{emp}<>;
{ // c::Chan<ms> * ms::Sess{c!int;;c?msg:double;;(c!1;;c!Addr;;c?Date or c!0)}<>
  send(c, id);
  // c::Chan<ms> * ms::Sess{c?msg:double;;(c!1;;c!Addr;;c?Date or c!0)}<>
  Double price = receive(c);
  // c::Chan<ms> * ms::Sess{c!1;;c!Addr;;c?Date or c!0)}<>
  if(price <= budget) {
    send(c, 1);
    send(c, a);
    Date sd = receive(c);
  } else send(c, 0);
}

// projection of G on S
pred G@S<a,b> ==
  a?int;a!double;(a?1;b!int;b!(Chan(a,ms) * Sess(ms,a?Addr;a!Date));a?Addr;a!Date \/ a?0);

void seller(Channel cb, Channel cs)
  requires cb::Chan<ms> * cs::Chan<ms> * ms::Sess{G@S<cb,cs>}<>
  ensures  cb::Chan<ms> * cs::Chan<ms> * ms::Sess{emp}<>;
{
  //cb::Chan<ms> * cs::Chan<ms> * ms::Sess{G@S<cb,cs>}<>
  //cb::Chan<ms> * cs::Chan<ms> * ms::Sess{cb?int;cb!double;(cb?1;cs!int;cs!(Chan(cb,ms) * Sess(ms,cb?Addr;cb!Date));cb?Addr;cb!Date \/ cb?0)}<>
  int id = receive(cb);
  //cb::Chan<ms> * cs::Chan<ms> * ms::Sess{cb!double;(cb?1;cs!int;cs!(Chan(cb,ms) * Sess(ms,cb?Addr;cb!Date));cb?Addr;cb!Date \/ cb?0)}<>
  send(cb; getPrice(id));
  //cb::Chan<ms> * cs::Chan<ms> * ms::Sess{(cb?1;cs!int;cs!(Chan(cb,ms) * Sess(ms,cb?Addr;cb!Date));cb?Addr;cb!Date \/ cb?0)}<>
  if(receive(cb) == 1){
    /* not sure how solve the disj issue at this point - assume we have a sol for it */
    //cb::Chan<ms> * cs::Chan<ms> * ms::Sess{cb?1;cs!int;cs!(Chan(cb,ms) * Sess(ms,cb?Addr;cb!Date));cb?Addr;cb!Date}<>
    send(cs; 1);
    //cb::Chan<ms> * cs::Chan<ms> * ms::Sess{cs!int;cs!(Chan(cb,ms) * Sess(ms,cb?Addr;cb!Date));cb?Addr;cb!Date}<>
    Prod p = getProd(id); 
    send(cs; p);
    //cb::Chan<ms> * cs::Chan<ms> * ms::Sess{cs!(Chan(cb,ms) * Sess(ms,cb?Addr;cb!Date));cb?Addr;cb!Date}<>
    send(cs; cb);
    //cb::Chan<ms> * cs::Chan<ms> * ms::Sess{cs!(Chan(cb,ms) * Sess(ms,cb?Addr;cb!Date));cb?Addr;cb!Date}<>
    cb = receive(cs);
  } else if(usr opt == 0)
    send(cs; 0);
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
 
