/* singly linked lists */

/* representation of a node */
data node {
	int val;
	node next
}

/* view for a singly linked list with all elements set to zero */
lz<L1> == self=null & L1=[||]
	or self::node<v, r> * r::lz<L2> & v=0 & L1=v:::L2;

/* append two singly linked lists */
void reverse(ref node xs, ref node ys)

	requires xs::lz<L1> * ys::lz<L2>
	ensures ys'::lz<L> & xs' = null;

{
	if (xs != null) {
		node tmp;
		tmp = xs.next;
		xs.next = ys;
		ys = xs;
		xs = tmp;
		reverse(xs, ys);
	}
}
