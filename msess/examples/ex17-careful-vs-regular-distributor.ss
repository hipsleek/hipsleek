hip_include 'msess/notes/node.ss'
hip_include 'msess/notes/hodef.ss'
hip_include 'msess/notes/fences.ss'
hip_include 'msess/notes/commprimitives.ss'
hip_include 'msess/notes/buyerseller.ss'

/* http://www.sewo.biz/UML2/UML2SequenceDiagrams.php */


pred_sess_prot G<B,S,Dc,Dr,cheap> ==  exists quot: B->S:id#id>=1 ;; S->B: price#price>0 & price=quot;;
                               ((B-> S: 1 ;; B->S:qty # qty>=0 ;; B->S: addr # addr::Addr<_>;;
                                 ((S->Dc: ship # ship::Addr<_> & quot>=cheap ) or (S->Dr:ship # ship::Addr<_> & quot<cheap)))
                                or (B-> S: 0));


void buyer(Channel c, int budget, int qty)
  requires  c::Chan{@S  G<B@prim,S@sec,Dc,Dr,_>}<> & budget>0 & qty>0
  ensures   c::Chan{emp}<>; //'
{
  int id = get_id();
  Addr a = get_addrs();
  send(c, id);
  int price = receive(c);
  if(price <= budget) {
    send(c, 1);
    send(c, qty);
    senda(c, a);
  } else {send (c, 0);}
  dprint;
}

void seller(Channel c, Channel dc, Channel dr, int bound)
  requires  c::Chan{@S  G<B@sec,S@prim,Dc,Dr,budget>}<> * dc::Chan{@S  G<B,S@prim,Dc@sec,Dr,budget>}<> * dr::Chan{@S  G<B,S@prim,Dc,Dr@sec,budget>}<> & bound>0
  ensures   c::Chan{emp}<> * dc::Chan{emp}<> * dr::Chan{emp}<> ;
{
  int id = receive(c);
  int price = get_price(id);
  send(c,price);
  int answ = receive(c);
  if(answ == 1) {
    int qty = receive(c);
    Addr addr = receivea(c);
    if (price<bound) {
      senda(dr,addr);
    }else {
      senda(dc,addr);
    }
  } else {send (c, 0);}
  dprint;
}
