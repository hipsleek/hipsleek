/* singly linked lists */
//../hip ex12-infer-shape-pre.ss --classic
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
  requires H(x)  ensures true;//H1(x);
*/
  infer[@shape_pre] requires true ensures true;

{
  if (x==null) 
    return 0;
  else {
    return 1+ size_helper(x.next);
  }
}


