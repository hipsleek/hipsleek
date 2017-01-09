struct node{
int val;
struct node *left;
struct node *right;
};

/*@
relation update(abstract T, node x, int d, node l, node r, abstract T1).
relation lookup(abstract T, node x, int d, node l, node r).

tree<T> == self = null
       or self::node<v,l,r> * l::tree<T> * r::tree<T>
	& lookup(T,self,v,l,r);

relation mark(abstract T,node x,abstract T1).

axiom true ==> mark(T,null,T).

axiom lookup(T,x,1,l,r) ==> mark(T,x,T).

axiom lookup(T,x,v,l,r) & update(T,x,1,l,r,T1) & v != 1 &
mark(T1,l,T2) & mark(T1,r,T2) ==> lookup(T2,x,1,l,r) & mark(T,x,T2).

*/

void mark(struct node *x)
/*@
requires x::tree<T>
ensures x::tree<T1> & mark(T,x,T1);
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
