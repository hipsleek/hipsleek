struct node{
int val;
struct node *left;
struct node *right;
};

/*@
relation update(abstract D, node x, int d, node l, node r, abstract D1).
relation lookup(abstract D, node x, int d, node l, node r).

dag<D> == self = null
	or self::node<v,l,r> * (l::dag<D> U* r::dag<D>)
	& lookup(D,self,v,l,r);

tree<T> == self = null
        or self::node<v,l,r> * l::tree<T> * r::tree<T>
        & lookup(T,self,v,l,r);

relation subset_edges(abstract T, abstract D).
relation reach_eq(abstract T, node x, abstract D).

//relation pr(abstract D, node x, bag(node) S).

//axiom true ==> pr(D,null,{}).

//axiom pr(D,l,Sl) & pr(D,r,Sr) & lookup(D,x,0,l,r) & S = union(Sl,Sr) ==> pr(D,x,S).

//axiom lookup(D,x,0,null,null) ==> pr(D,x,{x}).
 
rlemma x::tree<T> * x::dag<D> --@ (x::dag<D> U* y::dag<D>)
      &	subset_edges(T,D) & reach_eq(T,x,D)
      -> x::tree<T> * (x::dag<T> U* y::dag<T>);

relation unmarked(abstract D, node x).

axiom unmarked(D,x) ==> lookup(D,x,0,l,r) & unmarked(D,l) & unmarked(D,r).

*/

void spanning(struct node *x)
/*@
requires x::dag<D> & unmarked(D,x) & x != null
ensures x::tree<T> & subset_edges(T,D) & reach_eq(T,x,D);
*/
{
  struct node *l,*r;
  l = x->left;
  r = x->right;
  x->val = 1;
  if(l != NULL && l->val != 1)
    spanning(l);
  else x->left = NULL;
  if(r != NULL && r->val != 1)
    spanning(r);
  else x->right = NULL;
}
