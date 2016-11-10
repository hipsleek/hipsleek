data node{
  int val;
  node left;
  node right
}

relation update(abstract G, node x, int d, abstract G1).
relation lookup(abstract G, node x, int d, node l, node r).

relation span(abstract G1, node n, abstract G2).
relation cut(abstract G1, node x, int flag, abstract G2).

graph<G> == self = null
       or self::node<v,l,r> U* (l::graph<G> U* r::graph<G>)
	     & lookup(G,self,v,l,r);

rlemma "graph_gen_left_null" x::node<1,null,r> * (x::node<1,l,r> --@ (x::node<1,l,r> U* (r::graph<G1> U* 
	(l::node<1,l2,r2> U* (l2::graph<G1> U* r2::graph<G1>)))))
      	& lookup(G1,l,1,l2,r2) 
     -> x::node<1,null,r> U* r::graph<G2> & cut(G1,x,0,G2);

rlemma "graph_gen_right_null" x::node<1,l,null> * (x::node<1,l,r> --@ (x::node<1,l,r> U* (l::graph<G1> U* 
	(r::node<1,l2,r2> U* (l2::graph<G1> U* r2::graph<G1>)))))
      	& lookup(G1,r,1,l2,r2) 
     -> x::node<1,l,null> U* l::graph<G2> & cut(G1,x,1,G2);

rlemma "pttoupdate" x::node<v1,l,r> * (x::node<v,l,r> --@ (x::node<v,l,r> U* (l::graph<G> U* r::graph<G>)))
      & lookup(G,x,v,l,r) & update(G,x,v1,G1)
      -> x::node<v1,l,r> U* (l::graph<G1> U* r::graph<G1>);

rlemma "subgraphupdate_l" l::graph<G2> * (l::graph<G1> --@ (x::node<1,l,r> U* (l::graph<G1> U* r::graph<G1>))) 
       & lookup(G1,l,0,l2,r2) -> x::node<1,l,r> U* (l::graph<G2> U* r::graph<G2>) & lookup(G1,l,0,l2,r2) 
					& span(G1,l,G2); 

rlemma "subgraphupdate_r" r::graph<G2> * (r::graph<G1> --@ (x::node<1,l,r> U* (l::graph<G1> U* r::graph<G1>))) 
       & lookup(G1,r,0,l2,r2) -> x::node<1,l,r> U* (l::graph<G2> U* r::graph<G2>) & lookup(G1,r,0,l2,r2) 
					& span(G1,r,G2); 

axiom lookup(G,x,0,_,_) ==> x != null.

axiom true ==> span(G,null,G).

axiom lookup(G,x,v,l,r) & update(G,x,1,G1) & v != 1 & (span(G1,l,G2) | cut(G1,x,0,G2)) 
& (span(G2,r,G3) | cut(G2,x,1,G3)) ==> span(G,x,G3) & lookup(G3,x,1,l,r).

void spanning(node x)
requires x::graph<G> & lookup(G,x,0,_,_)
ensures x::graph<G1> & span(G,x,G1);
{
  node l,r;
  l = x.left;
  r = x.right;
  x.val = 1;
  if(l != null) {
    if(l.val == 0)
      spanning(l);
    else x.left = null;
  }
  if(r != null) {
    if(r.val == 0)
      spanning(r);
    else x.right = null;
  }
}