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
{send(c, id);
  Double price = receive(c);
  if(price <= budget) {
    send(c, 1);
    send(c, a);
    Date sd = receive(c);
  } else send(c, 0);
}

// projection of G on S
pred G@S<a,b> ==
  a?int;a!double;(a?1;b!int;b!(Chan(a,ms) * Sess(ms,a?Addr;a!Date)) \/ a?0);

void seller(Channel cb, Channel cs)
  requires cb::Chan<ms> * cs::Chan<ms> * ms::Sess{G@S<cb,cs>}<>
  ensures  cb::Chan<ms> * cs::Chan<ms> * ms::Sess{emp}<>;
{ int id = receive(cb); 
  send(cb; getPrice(id));
  int usr opt = receive(cb); 
  if(usr opt == 1){
    send(cs; 1); 
    Prod p = getProd(id); 
    send(cs; p);
    send(cs; cb);
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
  Prod p = receive(c);
  Channel cd = receive(c);
  Addr a = receive(cd);
  Date sd = cShip(a; p);
  send(cd; sd);
  send(c; cd);
}

