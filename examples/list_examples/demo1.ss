/* singly linked lists */

/* representation of a node */
data node {
	int val;
	node next
}

/* view for a singly linked list */
ll<L1> == self=null & L1=[||]
	or self::node<v, r> * r::ll<L2> & L1=v:::L2;

/* return the first element of a singly linked list*/
int ret_first(node x)

	requires x::ll<L> & len(L) > 0
	ensures res = head(L);
	
{
	return x.val;
}