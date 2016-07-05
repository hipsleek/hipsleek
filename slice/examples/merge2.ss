/* singly linked lists */

/* representation of a node */
data node {
	int val;
	node next
}

/* view for a singly linked list */
sort<L> == self=null & L=[||]
	or self::node<a, q> * q::sort<L1> & L=a:::L1 & ( L1=[||] | a <= head(L1) );

/* append two singly linked lists */
node merge(node x, node y)

	requires x::sort<L1> * y::sort<L2>
	ensures res::sort<L> & ( L1 != [||] & L2 != [||] & head(L) = min(head(L1), head(L2))
                          | L1 != [||] & L2 = [||] & L = L1
	                        | L1 = [||] & L2 != [||] & L = L2
                          | L1 = [||] & L2 = [||] & L = [||] );

{
	if (x == null) {
		return y;
	} else {
		if (y == null) {
			return x;
		} else {
			node r = null;
			if (x.val < y.val) {
				r = merge(x.next, y);
				x.next = r;
				return x;
			} else {
				r = merge(x, y.next);
				y.next = r;
				return y;
			}
		}
	}
}

/*
int maximum(int a, int b)

	requires true
	ensures res = max(a, b);

{
	if (a > b) {
		return a;
	} else {
		return b;
	}
}
*/
