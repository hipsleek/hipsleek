/* singly linked lists */

/* representation of a node */
data node {
	int val;
	node next
}

/* view for a singly linked list */
ll<n> == self = null & n = 0
	or self::node<_, r> * r::ll<m> & n = m + 1
	inv n >= 0;



/* return the first element of a singly linked list */
int ret_first(node x)

	requires x::ll<n> & x != null
	ensures true;
	
{
	return x.val;
}

/* return the first element of a singly linked list */
int ret_first2(node x)

	requires x::ll<n> & x != null
	ensures true;
	
{
	return x.val;
}

