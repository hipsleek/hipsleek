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

relation subset_reach(abstract D, node x, abstract D1).
relation eq_notreach(abstract D, node x, abstract D1).

rlemma x::dag<D1> * x::dag<D> --@ (x::dag<D> U* y::dag<D>)
      & subset_reach(D,x,D1) & eq_notreach(D,x,D1)
      -> x::dag<D1> U* y::dag<D1>;

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
*/

void mark(struct node *x)
/*@
requires x::dag<D>
ensures x::dag<D1> & mark(D,x,D1);
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
