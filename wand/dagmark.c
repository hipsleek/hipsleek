struct node{
int val;
struct node *left;
struct node *right;
};

/*@
relation update(bag(node) G, node x, int d, node l, node r, bag(node) G1).
relation lookup(bag(node) G, node x, int d, node l, node r).

dag<G> == self = null
       or self::node<v,l,r> * (l::dag<G> U* r::dag<G>)
	& lookup(G,self,v,l,r);

relation sub(bag(node) R, bag(node) R1,bag(node) G, bag(node) G1).
relation reach(bag(node) G, node x, bag(node) R).
relation notreach(bag(node) G, node x, bag(node) NR).

rlemma x::dag<G1> * x::dag<G> --@ (x::dag<G> U* y::dag<G>)
      & reach(G,x,R) & reach(G1,x,R1) 
      & sub(R,R1,G,G1) 
      & notreach(G,x,NR) & notreach(G1,x,NR)
      -> x::dag<G1> U* y::dag<G1>;

relation mark(bag(node) G,node x,bag(node) G1).

axiom true ==> mark(G,null,G).
axiom lookup(G,x,1,l,r) ==> mark(G,x,G).

axiom mark(G,x,G1) ==> reach(G,x,R) & reach(G1,x,R1) & sub(R,R1,G,G1).
axiom mark(G,x,G1) ==> notreach(G,x,NR) & notreach(G1,x,NR).

axiom lookup(G,x,v,l,r) & update(G,x,1,l,r,G1) & v != 1 & //v is unmarked skipped in paper
mark(G1,l,G2) & mark(G2,r,G3) ==> mark(G,x,G3) & lookup(G3,x,1,l,r).
*/

void mark(struct node *x)
/*@
requires x::dag<G>
ensures x::dag<G1> & mark(G,x,G1);
*/
{
struct node *l,*r;
if(x==NULL) return;
else {
  if (x->val == 1) return;
  l = x->left;
  r = x->right;
  x->val = 1;
  mark(l);
  mark(r);
}
//@dprint;
}
