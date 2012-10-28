/* singly linked lists */

/* representation of a node */

data node {
	int val; 
	node next;	
}



HeapPred H(node a).
HeapPred H1(node a).
HeapPred H2(node a, node b).
  HeapPred H3(node a, node b, node c).
/* append two singly linked lists */
HeapPred G(node a, node b).
HeapPred G1(node a).
HeapPred G2(node a, node b).
HeapPred G3(node a, node b, node c).

void append(ref node x, node y)
  infer [H2,G3]
  requires H2(x,y)
  ensures G3(x,x',y); //'
{
	if (x == null)
	      x = y;
	else 
		append(x.next, y);
}
