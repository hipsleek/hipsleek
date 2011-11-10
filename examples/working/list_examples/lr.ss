/* singly linked lists */

/* representation of a node */
data node {
	int val;
	node next
}

/* view for a singly linked list */
ll<L1> == self=null & L1=[||]
	or self::node<v, r> * r::ll<L2> & L1=app([| v |], L2);

lr<L1> == self=null & L1=[||]
	or self::node<v, r> * r::lr<L2> & L1=app(L2, [| v |]);

lemma self::ll<L1> <-> self::lr<L2> & L2 = rev(L1);

/* function to reverse a singly linked list */
void reverse(ref node xs, ref node ys)

	requires xs::ll<L1> * ys::ll<L2> 
	ensures ys'::ll<L> & L = app(rev(L1), L2);

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

void my_rev(ref node xs)

	requires xs::ll<L>
	ensures xs'::lr<L>;

{
	node ys = null;
	reverse(xs, ys);
	xs = ys;
}