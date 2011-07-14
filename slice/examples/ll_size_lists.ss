/* singly linked lists */

/* representation of a node */
data node {
	int val;
	node next
}

/* view for a singly linked list */
ll<n, L> == self = null & n = 0 & L = [||]
	or self::node<v, r> * r::ll<n1, L1> & v >= 0 & n = 1 + n1 & L = v:::L1
	inv n >= 0;
	
/* append two singly linked lists */
void append(node x, node y)

	requires x::ll<n1, L1> * y::ll<n2, L2> & len(L1) > 0
	ensures x::ll<n, L> & L = app(L1, L2) & n = n1 + n2;

{
	if (x.next == null) {
		x.next = y;
	} else {
		append(x.next, y);
	}
}

/* function to delete the node with value a in a singly linked list */
node delete_val(node x, int a)

	requires x::ll<n1, L1>
	ensures res::ll<n2, L2> & (a inlist L1 & len(L2) = len(L1) - 1 | a notinlist L1 & L1 = L2);
	
{
	if (x == null) {
		return x;
	} else {
		if (x.val == a) return x.next;
		else return new node(x.val, delete_val(x.next, a));
	}
}