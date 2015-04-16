struct node{
int val;
struct node *next;
};

/*@
relation update(abstract L, node x, int v, node p, abstract L1).
relation lookup(abstract L, node x, int v, node p).

relation mark(abstract L,node x,abstract L1).

ll<L> == self = null
      or self::node<v,p> * p::ll<L> & lookup(L,self,v,p);

axiom lookup(L,x,1,p) ==> mark(L,x,L).

axiom true ==> mark(L,null,L).

axiom lookup(L,x,v,p) & update(L,x,1,p,L1) & mark(L1,p,L2) & v != 1
 ==> lookup(L2,x,1,p) & mark(L,x,L2).
*/

void mark(struct node *x)
/*@
requires x::ll<L> 
ensures x::ll<L1> & mark(L,x,L1);
*/
{
if (x == NULL) return;
else {
	if(x->val == 1) return;
	x->val = 1;
	mark(x->next);
}
}
