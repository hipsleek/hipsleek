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
void append(node x, ref node y)

	requires x::ll<L1> * y::ll<L2> & len(L1) > 0
	ensures x::ll<L> & L = app(L1, L2) & y' = null;

{
	if (x.next == null) {
		x.next = y;
		y = null;
	} else {
		append(x.next, y);
	}
}

/* function to reverse a singly linked list */
void reverse(ref node xs, ref node ys)

	requires xs::ll<L1> * ys::ll<L2> 
	ensures ys'::ll<L> & L = app(rev(L1), L2) & xs' = null;

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

/* function to reverse two appended lists - or to append two reversed lists :) */
void app_rev(ref node l1, ref node l2)

	requires l1::ll<L1> * l2::ll<L2> & len(L1) > 0
	ensures l2'::ll<L> & L = app(rev(L2), rev(L1)) & l1' = null;

{
	append(l1, l2);
	reverse(l1, l2);
}
