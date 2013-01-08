/* singly linked lists */

/* representation of a node */
data node {
	int val;
	node next
}

/* view for a singly linked list */
ll<L1> == self=null & L1=[||]
	or self::node<v, r> * r::ll<L2> & L1=v:::L2;

void test(ref node x, ref node y)

	requires x::ll<L1> * y::ll<L2> & app(L1, L2) = [||]
	ensures x'::ll<L3> * y'::ll<L4> & alln(0, app(L3, L4)) & len(app(L3, L4)) = 2;

{
  if (x == null) {
    x = new node(0, null);
  } else {
    x.next = new node(0, null);
  }
  if (y == null) {
    y = new node(0, null);
  } else {
    y.next = new node(0, null);
  }
}
