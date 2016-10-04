hip_include 'msess/notes/node.ss'
hip_include 'msess/notes/hodef.ss'
hip_include 'msess/notes/commprimitives.ss'
hip_include 'msess/notes/fences.ss'

/* buyer - seller - shipper */
/* pred_prot G<B,S,H> == */
/*   B->S: id>=0;    //prod id */
/*   S->B: price>0; //price */
/*   (  B->S: 1;               */
/*      S->H: int    //prod id */
/*      B->H: Addr; H->B:Date; //replace delegation with direct communication */
/*   \/ B->S: 0;). */

/* buyer - seller - shipper */
/* pred_prot G<B,S,H> == */
/*   B->S: id>=0;    //prod id */
/*   S->B: price>0; //price */
/*   (  B->S: 1;      */
/*      F(1,q1)    */
/*      S->H: int    //prod id */
/*      BARRIER(H,B)  */   //-- can use * or barrier (with * you cannot know if shipper is awake?)
/*      B->H: Addr; H->B:Date; //replace delegation with direct communication */
/*   \/ B->S: 0;).    */

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

Channel start_shipper()
  requires true
  ensures  res::Chan{@S ?v#v>=1}<>;

void stop_shipper(Channel c)
  requires c::Chan{emp}<>
  ensures  true;

  
// projection of G on B:
/* pred_proj G@B<bs> == bs!int;;bs?msg:double;;(bs!1;;bs!Addr;;bs?Date or bs!0); */
pred_sess_tpproj GBS<> == !v#v>=1;;?v#v>0;;(!1 or !0);
pred_sess_tpproj GBH<> == !v#v::Addr<_> ;; ?v#v::DDate<_,_,_>;

void buyer(Channel c1, Channel c2, int budget)
  requires  [pr] c1::Chan{@S  !v#v>=1;;?v#v>0 & pr=v;;(!1 or !0)}<> * c2::Chan{@S !v#v::Addr<_> ;; ?v#v::DDate<_,_,_>}<> 
  ensures   c1::Chan{emp}<> * c2::Chan{emp}<> & pr<=budget or c1::Chan{emp}<> * c2::Chan{@S !v#v::Addr<_> ;; ?v#v::DDate<_,_,_>}<> & pr>budget; 
{
  int id = get_id();
  Addr a = get_addrs();
  send(c1, id);
  int price = receive(c1);
  if(price <= budget) {
    send(c1, 1);
    //some kind of barrier sync
    //...............
    senda(c2, a);
    DDate sd = received(c2);
  } else {send (c1, 0);}
  dprint;
}


pred_sess_tpproj GSa<> == ?v#v>=1;;!v#v>0;;((?1;;?v#v::Addr<_>;;!v#v::DDate<_,_,_>) or ?0);


void seller(ref Channel c1, Channel cs)
  requires c1::Chan{@S ?v#v>=1;;!v#v>0;;(?1 or ?0)}<> // * cs::Chan{@S GSb<>}<>
  ensures  c1::Chan{emp}<>;    // * cs'::Chan{emp}<>;
{
  int id = receive(c1);
  send(c1, get_price(id));
  int opt = receive(c1);
  if(opt == 1){
    Channel cs = start_shipper();
    send(cs, id);
    stop_shipper(cs);
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

