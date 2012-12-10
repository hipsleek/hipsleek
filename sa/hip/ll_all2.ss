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

ls<y> == self=y
  or self::node<_,q>*q::ls<y> & self!=y
inv true;

void append(ref node x, node y)
infer [H2,G3]
requires H2(x,y)
ensures G3(x,x',y); //'
  /* requires x::ls<null> */
  /* ensures x'::ls<y>; //' */
{
    if (x==null) { x = y;
    }
	else append(x.next, y);
}
