hip_include 'msess/notes/node.ss'
hip_include 'msess/notes/hodef.ss'
hip_include 'msess/notes/commprimitives.ss'

/* buyer - seller - shipper */
/* pred_prot G<B,S,H> == */
/*   B->S: id>=0;    //prod id */
/*   S->B: price>0; //price */
/*   (  B->S: 1; */
/*      S->H: int    //prod id */
/*      S->H: D(B->S: Addr; S->B:Date); //delegating to H the role of S */
/*   \/ B->S: 0;). */

int get_id()
  requires true
  ensures res>=1;

int get_budget()
  requires true
  ensures res>=0;

int get_price(int id)
  requires id>=1
  ensures res>0;

Addr get_addrs()
  requires true
  ensures res::Addr<_>;

Channel duplicate_channel(Channel cs)
  requires cs::Chan{@S %R}<>
  ensures cs::Chan{@S %R}<> * res::Chan{@S %R}<>;

// projection of G on B:
/* pred_proj G@B<bs> == bs!int;;bs?msg:double;;(bs!1;;bs!Addr;;bs?Date or bs!0); */
/* pred_sess_proj GB<> == !v#v>=1;;?v#v>0;;((!1;;!v#v::Addr<_>;;?v#v::DDate<_,_,_>) or !0); */

/* void buyer(Channel c, int budget) */
/*   requires  c::Chan{@S GB<>}<>  */
/*   ensures   c::Chan{emp}<>; */
/* { */
/*   int id = get_id(); */
/*   Addr a = get_addrs(); */
/*   send(c, id); */
/*   int price = receive(c); */
/*   if(price <= budget) { */
/*     send(c, 1); */
/*     senda(c, a); */
/*     DDate sd = received(c); */
/*   } else send(c, 0); */
/* } */

/* // projection of G on S */
/* pred G@S<a,b> == */
/*   a?int;a!double;(a?1;b!int;b!(Chan(a,ms) * Sess(ms,a?Addr;a!Date)) \/ a?0); */
pred_sess_proj GSa<> == ?v#v>=1;;!v#v>0;;((?1;;?v#v::Addr<_>;;!v#v::DDate<_,_,_>) or ?0);
pred_sess_proj GSb<> == !v#v>=1;;!v#v::Chan{@S ?v#v::Addr<_>;;!v#v::DDate<_,_,_>}<>;;?v#v::Chan{emp}<>;


void seller(ref Channel cb, ref Channel cs)
  requires cb::Chan{@S GSa<>}<> * cs::Chan{@S GSb<>}<>
  ensures  cb'::Chan{emp}<> * cs'::Chan{@S GSb<>}<>; //
{
  int id = receive(cb);
  send(cb, get_price(id));
  int opt = receive(cb);
  /* dprint; */
  if(opt == 1){
    Channel new_cs;
    new_cs = duplicate_channel(cs);
    dprint;
    send(new_cs, id);
    sendc(new_cs, cb);
    cb = receivec(new_cs);
  } 
}

/* // projection of G on H */
/* pred G@H<a> == */
/*   a?int;a?(Chan(b,ms) * Sess(ms,b?Addr;b!Date));a!(Chan(b,ms) * Sess(ms,emp)); */

/* /\* should the shipper listen for sellers in a loop? *\/ */
/* void shipper(Channel c) */
/*   requires c::Chan<ms> * ms::Sess{G@H<c>}<> */
/*   ensures  c::Chan<ms> * ms::Sess{emp}<>; */
/* { */
/*   Prod p = receive(c); */
/*   Channel cd = receive(c); */
/*   Addr a = receive(cd); */
/*   Date sd = cShip(a; p); */
/*   send(cd; sd); */
/*   send(c; cd); */
/* } */

