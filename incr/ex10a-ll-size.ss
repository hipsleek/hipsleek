/* singly linked lists */

/* representation of a node */
data node {
	int val;
	node next;
}

/* view for a singly linked list */
ll<n> == self = null & n = 0
	or self::node<_, q> * q::ll<n-1>
  inv n >= 0;

HeapPred H(node a).
//HeapPred G(node a, node b).
HeapPred H1(node a).


int size_helper(node x, ref int n)
  infer[H,H1]
  requires H(x)  ensures  true;//H1(x);
{
  if (x==null) 
    return n;
  else {
    n = n+1;
    return size_helper(x.next, n);
  }
}
