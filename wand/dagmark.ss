////============== dag.v ==================//
data node{
int val;
node left;
node right
}

relation update(abstract D, node x, int d, node l, node r, abstract D1).
relation lookup(abstract D, node x, int d, node l, node r).

dag<D> == self = null
       or self::node<v,l,r> * (l::dag<D> U* r::dag<D>)
	& lookup(D,self,v,l,r);

relation subset_reach(abstract D, node x, abstract D1).
relation eq_notreach(abstract D, node x, abstract D1).

rlemma "subdagupdate" l::dag<D1> * (l::dag<D> --@ (l::dag<D> U* r::dag<D>))
      & subset_reach(D,l,D1) & eq_notreach(D,l,D1)
      -> l::dag<D1> U* r::dag<D1>;

relation mark(abstract D,node x,abstract D1).

axiom true ==> mark(D,null,D).

axiom lookup(D,x,1,l,r) ==> mark(D,x,D).

axiom mark(D,x,D1) ==> subset_reach(D,x,D1) & eq_notreach(D,x,D1).

axiom lookup(D,x,v,l,r) & update(D,x,1,l,r,D1) & v != 1 & //v is unmarked skipped in paper
mark(D1,l,D2) & mark(D2,r,D3) ==> mark(D,x,D3) & lookup(D3,x,1,l,r).

axiom lookup(D,x,v,l,r) & update(D,x,1,l,r,D1) & v != 1 & //v is unmarked skipped in paper
mark(D1,r,D2) & mark(D2,l,D3) ==> mark(D,x,D3) & lookup(D3,x,1,l,r).

axiom lookup(D,x,v,l,r) & mark(D,l,D1) & v != 1
& mark(D1,r,D2) & update(D2,x,1,l,r,D3) ==> mark(D,x,D3) & lookup(D3,x,1,l,r).

axiom lookup(D,x,v,l,r) & mark(D,r,D1) & v != 1
& mark(D1,l,D2) & update(D2,x,1,l,r,D3) ==> mark(D,x,D3) & lookup(D3,x,1,l,r).

axiom lookup(D,x,v,l,r) & mark(D,l,D1) & v != 1
& mark(D2,r,D3) & update(D1,x,1,l,r,D2) ==> mark(D,x,D3) & lookup(D3,x,1,l,r).

axiom lookup(D,x,v,l,r) & mark(D,r,D1) & v != 1
& mark(D2,l,D3) & update(D1,x,1,l,r,D2) ==> mark(D,x,D3) & lookup(D3,x,1,l,r).

void mark(node x)
requires x::dag<D>
ensures x::dag<D1> & mark(D,x,D1);
{
node l,r;
if(x==null) return;
else {
//[x::node<v,l,r> * dag(l,G) U* dag(r,G)  /\ d(x,v,l,r,G) |- x::node<v@L,_,_ >  // BIND]
  if (x.val == 1) return;
//assume false;
//[x::node<v,l,r> * dag(l,G) U* dag(r,G) /\ d(x,v,l,r,G) |- x::node<_,l@L,_>   // BIND]
  l = x.left;
//[x::node<v,l,r> * dag(l,G) U* dag(r,G)  /\ d(x,v,l,r,G) |- x::node<_,_,r@L>  // BIND]
  r = x.right;
//[x::node<v,l,r> * dag(l,G) U* dag(r,G) /\ d(x,v,l,r,G) |- x::node<v@M,_,_ >  // BIND]
  x.val = 1;
//[x::node<1,l,r> * dag(l,G) U* dag(r,G) /\ d(x,1,l,r,G) |- dag(l,G)   // PRE]
//[x::node<1,l,r> * (dag(l,G) --@ dag(l,G) U* dag(r,G)) // Residue]
//dprint;
  mark(l);
  mark(r);
//dprint;
//[x::node<1,l,r> * (dag(l,G) --@ dag(l,G) U* dag(r,G)) * dag(l,G1) // Add PostCondition]
//[x::node<1,l,r> * dag(l,G1) U* dag(r,G1) // Apply Ramification Lemma]
//[x::node<1,l,r> * dag(l,G1) U* dag(r,G1) /\ mark(G,l,G1) /\ d(x,1,l,r,G) |- dag(r,G1)   // PRE]
//[x::node<1,l,r> * (dag(r,G1) --@ dag(l,G1) U* dag(r,G1)) // Residue]

//dprint;
//[x::node<1,l,r> * (dag(r,G1) --@ dag(l,G1) U* dag(r,G1)) * dag(r,G2)// Add PostCondition]
//[x::node<1,l,r> * dag(l,G2) U* dag(r,G2) // Apply Ramification Lemma]
//[x::node<1,l,r> * dag(l,G2) U* dag(r,G2) /\ mark(G,l,G1) /\ mark(G1,r,G2) /\ d(x,1,l,r,G) |- dag(x,G2) /\ mark(G,x,G2) // POST]
}
//dprint;
}
