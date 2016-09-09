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

sll<> == self = null 
	or self::node<_, q> * q::sll<>
  inv true;

HeapPred H(node a).
//HeapPred G(node a, node b).
HeapPred H1(node a).


int size_helper(node x)
/*
  infer[H]
  requires x::sll<>  ensures H(x);
*/
  infer[@shape_post] requires  x::sll<> ensures true;

{
  if (x==null) 
    return 0;
  else {
    return 1+ size_helper(x.next);
  }
}


