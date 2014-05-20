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

relation subset_reach(abstract D, node x, abstract D1).
relation eq_notreach(abstract D, node x, abstract D1).

rlemma x::dag<D1> * x::dag<D> --@ (x::dag<D> U* y::dag<D>)
      & subset_reach(D,x,D1) & eq_notreach(D,x,D1)
      -> x::dag<D1> U* y::dag<D1>;

relation unmarked(abstract D).

*/

void spanning(struct node *x)
/*@
requires x::dag<D> & unmarked(D);
ensures x::tree<T> & subset_edges(T,D) & reach_eq(T,x,D);
*/
{
struct node *l,*r;
 l = x->left;
 r = x->right;
 if(l !=NULL && l->val != 1)
  spanning(l);
 else x->left = 0;
 if(r != NULL && r->val !=1)
  spanning(r);
 else x->right = 0;
}
