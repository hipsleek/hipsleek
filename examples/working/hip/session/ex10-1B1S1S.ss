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

DDate get_date(Addr a, int prod_id)
  requires a::Addr<_> & prod_id >=1
  ensures  a::Addr<_> * res::DDate<_,_,_>;

// projection of G on B:
/* pred_proj G@B<bs> == bs!int;;bs?msg:double;;(bs!1;;bs!Addr;;bs?Date or bs!0); */
pred_sess_tpproj GB<> == !v#v>=1;;?v#v>0;;((!1;;!v#v::Addr<_>;;?v#v::DDate<_,_,_>) or !0);

void buyer(ref Channel c, int budget)
  requires  c::Chan{@S GB<>}<>
  ensures   c'::Chan{emp}<>; //'
{
  int id = get_id();
  Addr a = get_addrs();
  send(c, id);
  int price = receive(c);
  if(price <= budget) {
    send(c, 1);
    senda(c, a);
    DDate sd = received(c);
  } else {send (c, 0);}
  dprint;
}

/* // projection of G on S */
/* pred G@S<a,b> == */
/*   a?int;a!double;(a?1;b!int;b!(Chan(a,ms) * Sess(ms,a?Addr;a!Date)) \/ a?0); */
pred_sess_tpproj GSa<> == ?v#v>=1;;!v#v>0;;((?1;;?v#v::Addr<_>;;!v#v::DDate<_,_,_>) or ?0);
pred_sess_tpproj GSb<> == (!1;;!v#v>=1;;!v#v::Chan{@S ?v#v::Addr<_>;;!v#v::DDate<_,_,_>}<>;;?v#v::Chan{emp}<>) or (!0);


void seller(ref Channel cb, ref Channel cs)
  requires cb::Chan{@S GSa<>}<> * cs::Chan{@S GSb<>}<>
  ensures  cb'::Chan{emp}<> * cs'::Chan{emp}<>;
{
  int id = receive(cb);
  send(cb, get_price(id));
  int opt = receive(cb);
  if(opt == 1){
    send(cs, opt);
    send(cs, id);
    dprint;
    sendc(cs, cb);
    cb = receivec(cs);
  } else {
    send(cs, opt);
  }
}

/* // projection of G on H */
/* pred G@H<a> == */
/*   a?int;a?(Chan(b,ms) * Sess(ms,b?Addr;b!Date));a!(Chan(b,ms) * Sess(ms,emp)); */
pred_sess_tpproj GS<> ==
  ?v#v>=1;;?v#v::Chan{@S ?v#v::Addr<_>;;!v#v::DDate<_,_,_>}<>;;!v#v::Chan{emp}<>;


/* should the shipper listen for sellers in a loop? */
void shipper(Channel c)
  requires c::Chan{@S GS<>}<>
  ensures  c::Chan{emp}<>;
{
  int prod = receive(c);
  Channel cd = receivec(c);
  Addr a = receivea(cd);
  dprint;
  DDate sd = get_date(a, prod);
  sendd(cd, sd);
  sendc(c, cd);
}
