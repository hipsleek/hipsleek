struct node{
int val;
struct node* next;
};

/*@
relation update(bag(node) L, node x, int v, node p, bag(node) L1).
relation lookup(bag(node) L, node x, int v, node p).

relation mark(bag(node) L,node x,bag(node) L1).
relation mark1(bag(node) L,node x,bag(node) L1).

ll<L> == self = null
      or self::node<v,p> * p::ll<L> & lookup(L,self,v,p);

axiom lookup(L,x,1,p) ==> mark(L,x,L).
//axiom L = L1 ==> mark(L,null,L1).
//axiom mark(L,null,L1) ==> L = L1.
//axiom lookup(L1,x,1,p) ==> update(_,x,1,p,L1).
axiom lookup(L,x,v,p) & update(L,x,1,p,L1) & mark(L1,p,L2) ==> lookup(L2,x,1,p).
*/

void mark(struct node* x)
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
