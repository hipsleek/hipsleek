/* singly linked lists */

/* representation of a node */
data node {
	int val;
	node next
}

/* view for a singly linked list */
ll<L1> == self=null & L1=[||]
	or self::node<v, r> * r::ll<L2> & L1=v:::L2;

/* append two singly linked lists */
void append(node x, node y)

	requires x::ll<L1> * y::ll<L2> & len(L1) > 0 & alln(0, app(L1, L2))
	ensures x::ll<L> & len(L) = len(L1) + len(L2) & alln(0, rev(L));

{
	if (x.next == null) {
		x.next = y;
	} else {
		append(x.next, y);
	}
}
