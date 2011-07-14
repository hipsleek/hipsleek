/* singly linked lists */

/* representation of a node */
data node {
	int val;
	node next
}

/* view for a singly linked list */
ll<L1> == self=null & L1=[||]
	or self::node<v, r> * r::ll<L2> & L1=v:::L2;

/* function to delete the node with value a in a singly linked list */
node delete_val(node x, int a)

	requires x::ll<L1>
	ensures res::ll<L2> & (a inlist L1 & len(L2) = len(L1) - 1 | a notinlist L1 & a:::L1 = a:::L2);
	
{
	if (x == null) {
		return x;
	} else {
		if (x.val == a) return x.next;
		else return new node(x.val, delete_val(x.next, a));
	}
}
