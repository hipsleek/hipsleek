data node {
	int val;
	node next
}

/* view for a singly linked list */
ll<L1> == self = null & L1 = [||]
	or self::node<v, r> * r::ll<L2> & L1 = v:::L2;


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


/* function to insert a node in a singly linked list */
void insert(node x, int a)

	requires x::ll<L1> & len(L1) > 0
	ensures x::ll<L2> & L2 = app(L1, [|a|]);
	
{
	if (x.next == null) {
		x.next = new node(a, null);
	} else {
		insert(x.next, a);
	}
} 
