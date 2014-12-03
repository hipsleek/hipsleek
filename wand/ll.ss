/* singly linked lists */

/* representation of a node */
data node {
	int val;
	node next
}

relation cons(abstract L, int v, abstract Lt).

relation reverse(abstract L, abstract L1).

relation append(abstract L, abstract L1, abstract L2).

relation isempty(abstract L).

axiom cons(L,v,Lp) ==> !(isempty(L)).

axiom isempty(L) ==> append(L1,L,L1). 

axiom isempty(L) ==> reverse(L,L).

axiom cons(L,v,Lt) & reverse(Tr,Lt) ==> append(Lr,Tr,Lv) & reverse(Lr,L) & cons(Lv,v,Le) & isempty(Le).

axiom cons(L,v,Lt) & append(Lt,L1,L2) & cons(La,v,L1) ==> cons(La,v,Lt) & append(L,La,L2).

/* view for a singly linked list */
ll<L> == self=null & isempty(L)
      or self::node<v, p> * p::ll<Lp> & cons(L,v,Lp)
      inv (self=null & isempty(L) | self!=null & !(isempty(L)));

/* function to reverse a singly linked list */
void reverse_list(ref node xs, ref node ys)

	requires xs::ll<L1> * ys::ll<L2> 
	ensures ys'::ll<L> & append(L, Lr, L2) & reverse(Lr, L1) & xs' = null;

{
	if (xs != null) { 
		node tmp;
		tmp = xs.next;
		xs.next = ys;
		ys = xs;
		xs = tmp; 
		reverse_list(xs, ys);
	}
}

/* append two singly linked lists */
void append_list(node x, node y)

    requires x::ll<L1> * y::ll<L2> & x != null
	ensures x::ll<L> & append(L, L1, L2) ;

{
	if (x.next == null) {
		x.next = y;
	} else {
		append_list(x.next, y);
	}
}
