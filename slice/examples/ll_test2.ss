/* NOT WORKING... */

/* singly linked lists */

/* representation of a node */
data node {
	int val;
	node next
}

/* view for a singly linked list */
ll<L1> == self=null & L1=[||]
	or self::node<v, r> * r::ll<L2> & L1=v:::L2;

/* function to delete the a-th node in a singly linked list */
void delete(node x, int a)

	requires x::ll<L1> & len(L1) > a & a > 0 
	ensures x::ll<L2> & exists (La, Lm, Lb: L1 = app(La, Lm, Lb) & len(Lm) = 1);

{
	if (a == 1) {
		x.next = x.next.next;
	} else {
		delete(x.next, a-1);
	}	
}
