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

pred_sess_proj GSa<> == ?v#v::Addr<_>;;!v#v::DDate<_,_,_>;
pred_sess_proj GSb<> == !v#v::Chan{@S ?v#v::Addr<_>;;!v#v::DDate<_,_,_>}<>;;?v#v::Chan{emp}<>;


void seller(ref Channel cb,  Channel cs)
  requires cb::Chan{@S GSa<>}<> * cs::Chan{@S GSb<>}<>
  ensures  cb'::Chan{emp}<> * cs::Chan{emp}<>; //'
{

    dprint;
    sendc(cs, cb);
    dprint;
    cb = receivec(cs);
    dprint;
}

