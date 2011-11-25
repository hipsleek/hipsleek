/* singly linked lists */

/* representation of a node */
data node {
	int val;
	node next
}

/* view for a singly linked list */
ll<L1> == self=null & L1=[||]
	or self::node<v, r> * r::ll<L2> & L1=v:::L2;

void mk_zero(ref node x)

  requires x::ll<L1>
  ensures x::ll<L2> & alln(0, L2);

{
  if (x != null) {
    x.val = 0;
    if (x.next != null) {
      x.next.val = 0;
      mk_zero(x.next.next);
    }
  }
} 