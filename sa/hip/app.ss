data node {
	int val; 
	node next;	
}

HeapPred H(node a).
HeapPred K(node a).
HeapPred H3(node a).
HeapPred H4(node a).
HeapPred G1(node a, node b).
HeapPred G(node a, node b).

/*
ls<> == self=null 
  or self::node<_,q>*q::ls<>
 inv true;
*/

void append(node x, node y)
/*
  requires x::ls<> * y::ls<> & x!=null
  ensures x'::ls<>;
  infer [H,K,G]
  requires H(x)*K(y)
  ensures G(x,y);//'
*/
  infer [H,G]
  requires H(x)
  ensures G(x,y);//'
{
	if (x.next == null) x.next = y;	
	else append(x.next, y);
}


