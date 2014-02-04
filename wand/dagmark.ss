data node{
int val;
node left;
node right
}

relation mark(bag(node) G,int x,bag(node) G1).
relation mark1(bag(node) G,int x,bag(node) G1).
relation update(bag(node) G, node x, int d, node l, node r,bag(node) G1).
relation reach(bag(node) G, node x, bag(node) R).

dag<G> == self = null
       or self::node<v,l,r> * l::dag<G> U* r::dag<G> & update(G,self,v,l,r,G1);

axiom update(G,x,1,l,r,G1) ==> mark1(G,x,G1).

axiom mark(G,x,G1) ==> reach(G,x,R) & reach(G1,x,R1) & R subset R1.
axiom mark(G,x,G1) ==> !(reach(G,x,R)) & !(reach(G1,x,R)).

axiom mark(G,x,G1) & mark(G1,y,G2) ==> mark(G,y,G1) & mark(G1,x,G2).
axiom mark(G,l,G1) & mark(G1,r,G2) & mark1(G2,x,G3) ==> mark(G,x,G3).
axiom mark(G,r,G1) & mark1(G1,x,G2) & mark(G2,l,G3) ==> mark(G,x,G3).
axiom mark(G,l,G1) & mark1(G1,x,G2) & mark(G2,r,G3) ==> mark(G,x,G3).
axiom mark1(G,x,G1) & mark(G1,l,G2) & mark(G2,r,G3) ==> mark(G,x,G3).

//ramification lemma dag(l,G) --@ (dag(l,G) U* dag(r,G)) * dag(l,G1) 
// & reach(G,l,R) & reach(G1,l,R1) & R subset R1 & !reach(G,l,R) & !reach(G1,l,R1)
// -> dag(l,G1) U* dag(r,G1) & mark(G,l,G1) 

void mark(node x)
requires x::dag<G>
ensures x::dag<G1> & mark(G,x,G1);
{
node l,r;
if(x==null) return;
else {
//[x::node<v,l,r> * dag(l,G) U* dag(r,G)  /\ d(x,v,l,r,G) |- x::node<v@L,_,_ >  // BIND]
  if (x.val == 1) return;
//[x::node<v,l,r> * dag(l,G) U* dag(r,G) /\ d(x,v,l,r,G) |- x::node<_,l@L,_>   // BIND]
  l = x.left;
//[x::node<v,l,r> * dag(l,G) U* dag(r,G)  /\ d(x,v,l,r,G) |- x::node<_,_,r@L>  // BIND]
  r = x.right;
//[x::node<v,l,r> * dag(l,G) U* dag(r,G) /\ d(x,v,l,r,G) |- x::node<v@M,_,_ >  // BIND]
  x.val = 1;
//[x::node<1,l,r> * dag(l,G) U* dag(r,G) /\ d(x,1,l,r,G) |- dag(l,G)   // PRE]
//[x::node<1,l,r> * (dag(l,G) --@ dag(l,G) U* dag(r,G)) // Residue]
  mark(l);
//[x::node<1,l,r> * (dag(l,G) --@ dag(l,G) U* dag(r,G)) * dag(l,G1) // Add PostCondition]
//[x::node<1,l,r> * dag(l,G1) U* dag(r,G1) // Apply Ramification Lemma]
//[x::node<1,l,r> * dag(l,G1) U* dag(r,G1) /\ mark(G,l,G1) /\ d(x,1,l,r,G) |- dag(r,G1)   // PRE]
//[x::node<1,l,r> * (dag(r,G1) --@ dag(l,G1) U* dag(r,G1)) // Residue]
  mark(r);
//[x::node<1,l,r> * (dag(r,G1) --@ dag(l,G1) U* dag(r,G1)) * dag(r,G2)// Add PostCondition]
//[x::node<1,l,r> * dag(l,G2) U* dag(r,G2) // Apply Ramification Lemma]
//[x::node<1,l,r> * dag(l,G2) U* dag(r,G2) /\ mark(G,l,G1) /\ mark(G1,r,G2) /\ d(x,1,l,r,G) |- dag(x,G2) /\ mark(G,x,G2) // POST]
}
}
