/* singly linked lists */

/* representation of a node */
data node {
	int val;
	node next
}

relation lookup(abstract L, node x, int v, node p, abstract Lp).

relation reverse(abstract L1, abstract L2).

relation append(abstract L1, abstract L2, abstract L3).

relation isempty(abstract L).

axiom x = null ==> lookup(L,x,_,_,_) & isempty(L).

axiom isempty(L) ==> append(L1,L,L1). 

axiom isempty(L) ==> reverse(L,L).

/* view for a singly linked list */
ll<L> == self=null & isempty(L)
	or self::node<v, p> * p::ll<Lp> & lookup(L,self,v,p,Lp) ;

/* function to reverse a singly linked list */
void reverse_list(ref node xs, ref node ys)

	requires xs::ll<L1> * ys::ll<L2> 
	ensures ys'::ll<L> & append(L, Lr, L2) & reverse(L1, Lr) & xs' = null;

{
	if (xs != null) { //assume false;
		node tmp;
		tmp = xs.next;
		xs.next = ys;
		ys = xs;
		xs = tmp;
		reverse_list(xs, ys);
	}
}
