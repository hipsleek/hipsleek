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

rlemma x::node<v1,l1,r1> * x::node<v,l,r> --@ 
	(x::node<v,l,r> U* (l::graph<G> U* r::graph<G>))
	& lookup(G,x,v,l,r) & update(G,x,v1,l1,r1,G1) 
      -> x::node<v1,l1,r1> U* (l1::graph<G1> U* r1::graph<G1>);

rlemma x::graph<G1> * x::graph<G> --@ (x::graph<G> U* y::graph<G>)
      & subset_reach(G,x,G1) & eq_notreach(G,x,G1)
      -> x::graph<G1> U* y::graph<G1>;

relation mark(abstract G,node x,abstract G1).

axiom true ==> mark(G,null,G).

axiom lookup(G,x,1,l,r) ==> mark(G,x,G).

axiom mark(G,x,G1) ==> subset_reach(G,x,G1) & eq_notreach(G,x,G1).

axiom lookup(G,x,v,l,r) & update(G,x,1,l,r,G1) & v != 1 & //v is unmarked skipped in paper
mark(G1,l,G2) & mark(G2,r,G3) ==> mark(G,x,G3) & lookup(G3,x,1,l,r).

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
