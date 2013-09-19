/* representation of a node */
data node {
	int val; 
	node left;
	node right;	
}

/* dag predicate */
dag<G> == self = null
     or self::node<_,l,r> * l::dag<G> U* r::dag<G>;

/* uninterpreted relations */
relation reach(bag(node) G, node x, bag(node) R).
relation notreach(bag(node) G, node x, bag(node) NR).
relation mark(bag(node) G, node x, bag(node) Gm).
relation update(bag(node) G, node x, int d, node l, node r, bag(node) Gm).

axiom mark(G,x,Gm) ==> reach(Gm,x,Rm) & reach(G,l,R) & R subset Rm.
axiom mark(G,x,Gm) ==> notreach(Gm,x,NR) & notreach(G,l,NR) & NR = NRm.

axiom mark(G,x,Gm) & mark(Gm,y,Gmm) ==> mark(G,y,Gm) & mark(Gm,x,Gmm).
axiom mark(G,l,Gm) & mark(Gm,r,Gmm) & update(Gmm,x,d,l,r,Gmmm) ==> mark(G,x,Gmmm).
axiom mark(G,r,Gm) & update(Gm,x,d,l,r,Gmm) & mark(Gmm,l,Gmmm)==> mark(G,x,Gmmm).
axiom mark(G,l,Gm) & update(Gm,x,d,l,r,Gmm) & mark(Gmm,r,Gmmm)==> mark(G,x,Gmmm).
axiom update(G,x,d,l,r,Gm) & mark(Gm,l,Gmm) & mark(Gm,r,Gmmm) ==> mark(G,x,Gmmm).


lemma l::dag<Gm> * l::dag<G> -* (l::dag<G> U* r::dag<G>) 
	& reach(G,l,R) & reach(Gm,l,Rm) & R subset Rm 
	& notreach(G,l,NR) & notreach(Gm,l,NRm) & NR = NRm
	-> l::dag<Gm> U* r::dag<Gm>;

lemma x::node<d,l,r> * l::dag<G> U* r::dag<G> -> x::dag<Gm> & update(G,x,d,l,r,Gm);
// lemma self::dag<G> -> self::dag<Gm> & update(G,x,d,l,r,Gm);

void mark(ref node x)
requires x::dag<G>
ensures x::dag<Gm> & mark(G,x,Gm);
{
node l,r;
if(x == null) return;
else {
if (x.val == 1) return;
   l = x.left;
   r = x.right;
   x.val = 1;
   mark(l);
   mark(r);
  }
}

