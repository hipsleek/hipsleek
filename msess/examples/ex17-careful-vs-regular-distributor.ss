hip_include 'msess/notes/node.ss'
hip_include 'msess/notes/hodef.ss'
hip_include 'msess/notes/fences.ss'
hip_include 'msess/notes/commprimitives.ss'
hip_include 'msess/notes/buyerseller.ss'

/* http://www.sewo.biz/UML2/UML2SequenceDiagrams.php */


pred_sess_prot G<B,S,Dc,Dr,cheap> ==  B->S:id#id>=0 ;; S->B: price#price>0 & price=quot;;
                               ((B-> S: 1 ;; B->S:qty # qty>=0 ;; B->S: addr # addr::Addr<_>;;
                                 ((S->Dc: ship # ship::Addr<_> & quot>=cheap ) or (S->Dr:ship # ship::Addr<_> & quot<cheap)))
                                or (B-> S: 0));


pred ll<> == exists x: (self =x);

/*
void buyer(ref Channel c, int budget)
  requires  c::Chan{@S  G<B@prim,S@sec,Dc,Dr,budget>}<> 
  ensures   c::Chan{emp}<>; //'
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
*/
