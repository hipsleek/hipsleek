data node {
	int val;
	node next
}

HeapPred H(node a).
  HeapPred G(node a, node b).


/* return the tail of a singly linked list */
node get_next(node x)
  infer[H,G]
  requires H(x)
  ensures G(x,res);//'

{
  if (x==null) return null;
  else return x.next;
}


