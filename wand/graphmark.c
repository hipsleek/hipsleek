struct node{
int val;
struct node *left;
struct node *right;
};

/*@
relation update(abstract G, node x, int d, node l, node r, abstract G1).
relation lookup(abstract G, node x, int d, node l, node r).

graph<G> == self = null
       or self::node<v,l,r> U* (l::graph<G> U* r::graph<G>)
	& lookup(G,self,v,l,r);

relation subset_reach(abstract G, node x, abstract G1).
relation eq_notreach(abstract G, node x, abstract G1).

rlemma l::graph<G1> * l::graph<G> --@ (x::node<v,l,r> U* (l::graph<G> U* r::graph<G>))
      & subset_reach(G,l,G1) & eq_notreach(G,l,G1) & lookup(G,x,v,l,r) & lookup(G1,x,_,l,r)
      -> x::node<_,l,r> U* (l::graph<G1> U* r::graph<G1>);

rlemma r::graph<G1> * r::graph<G> --@ (x::node<v,l,r> U* (l::graph<G> U* r::graph<G>))
      & subset_reach(G,r,G1) & eq_notreach(G,r,G1) & lookup(G,x,v,l,r) & lookup(G1,x,_,l,r)
      -> x::node<_,l,r> U* (l::graph<G1> U* r::graph<G1>);

rlemma x::node<v1,l,r> * x::node<v,l,r> --@ (x::node<v,l,r> U* (l::graph<G> U* r::graph<G>))
      & lookup(G,x,v,l,r)
      -> x::node<v1,l,r> U* (l::graph<G1> U* r::graph<G1>);

relation mark(abstract G,node x,abstract G1).

axiom true ==> mark(G,null,G).

axiom lookup(G,x,1,l,r) ==> mark(G,x,G).

axiom mark(G,x,G1) ==> subset_reach(G,x,G1) & eq_notreach(G,x,G1).

axiom mark(G,x,G1) & lookup(G,y,v,l,r) ==> subset_reach(G,x,G1) & eq_notreach(G,x,G1) & lookup(G1,y,_,l,r).

axiom lookup(G,x,v,l,r) & update(G,x,1,l,r,G1) & v != 1 & //v is unmarked skipped in paper
mark(G1,l,G2) & mark(G2,r,G3) ==> mark(G,x,G3) & lookup(G3,x,1,l,r).

axiom lookup(G,x,v,l,r) & update(G,x,1,l,r,G1) & v != 1 & //v is unmarked skipped in paper
mark(G1,r,G2) & mark(G2,l,G3) ==> mark(G,x,G3) & lookup(G3,x,1,l,r).

axiom lookup(G,x,v,l,r) & mark(G,l,G1) & v != 1
& mark(G1,r,G2) & update(G2,x,1,l,r,G3) ==> mark(G,x,G3) & lookup(G3,x,1,l,r).

axiom lookup(G,x,v,l,r) & mark(G,r,G1) & v != 1
& mark(G1,l,G2) & update(G2,x,1,l,r,G3) ==> mark(G,x,G3) & lookup(G3,x,1,l,r).

axiom lookup(G,x,v,l,r) & mark(G,l,G1) & v != 1
& mark(G2,r,G3) & update(G1,x,1,l,r,G2) ==> mark(G,x,G3) & lookup(G3,x,1,l,r).

axiom lookup(G,x,v,l,r) & mark(G,r,G1) & v != 1
& mark(G2,l,G3) & update(G1,x,1,l,r,G2) ==> mark(G,x,G3) & lookup(G3,x,1,l,r).

*/

void mark(struct node *x)
/*@
requires x::graph<G>
ensures x::graph<G1> & mark(G,x,G1);
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
}
