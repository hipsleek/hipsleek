data node{
node mark;
node left;
node right
}

relation update(abstract G, node x, int d, abstract G1).
relation lookup(abstract G, node x, int d, node l, node r).

graph<G> == self = null
       or self::node<v,l,r> U* (l::graph<G> U* r::graph<G>)
	& lookup(G,self,v,l,r);

relation subset_reach(abstract G, node x, abstract G1).
relation eq_notreach(abstract G, node x, abstract G1).

rlemma "subgraphupdate_l" l::graph<G1> * (l::graph<G> --@ (x::node<v,l,r> U* (l::graph<G> U* r::graph<G>)))
      & subset_reach(G,l,G1) & eq_notreach(G,l,G1) & lookup(G,x,v,l,r) & lookup(G1,x,v1,l,r)
      -> x::node<v1,l,r> U* (l::graph<G1> U* r::graph<G1>);

rlemma "subgraphupdate_r" r::graph<G1> * (r::graph<G> --@ (x::node<v,l,r> U* (l::graph<G> U* r::graph<G>)))
      & subset_reach(G,r,G1) & eq_notreach(G,r,G1) & lookup(G,x,v,l,r) & lookup(G1,x,v1,l,r)
      -> x::node<v1,l,r> U* (l::graph<G1> U* r::graph<G1>);

rlemma "pttoupdate" x::node<v1,l,r> * (x::node<v,l,r> --@ (x::node<v,l,r> U* (l::graph<G> U* r::graph<G>)))
      & lookup(G,x,v,l,r) & update(G,x,v1,G1)
      -> x::node<v1,l,r> U* (l::graph<G1> U* r::graph<G1>);

relation mark(abstract G,node x,abstract G1).

axiom true ==> mark(G,null,G).

axiom lookup(G,x,1,l,r) ==> mark(G,x,G).

axiom mark(G,x,G1) & lookup(G,y,v,l,r) ==> subset_reach(G,x,G1) & eq_notreach(G,x,G1) & lookup(G1,y,_,l,r).

axiom lookup(G,x,v,l,r) & update(G,x,1,G1) & v != 1 & //v is unmarked skipped in paper
mark(G1,l,G2) & mark(G2,r,G3) ==> mark(G,x,G3) & lookup(G3,x,1,l,r).

node copy(node x)
requires x::graph<G>
ensures x::graph<G1> ;
{
  node l, r, x0, l0, r0;
  if(x == null) 
    return null;
  x0 = x.mark;
  if(x0 != null)
    return x0;
  x0 = new node(null, null, null);
  l = x.left;
  r = x.right;
  x.mark = x0;
  l0 = copy(l);
  x0.left = l0;
  r0 = copy(r);
  x0.right = r0;
  return x0;
}

