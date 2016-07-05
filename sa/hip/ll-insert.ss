data node {
	int val; 
	node next;	
}


/* view for a singly linked list */
/*
ll<> == self = null
	or self::node<_, q> * q::ll<>
  inv true;
*/
HeapPred H1(node a).
HeapPred G1(node a).
void insert(node x, int a)
  /* requires x::node<_,p> * p::ll<> */
  /* ensures x::node<_,p1> * p1::ll<>; */
  infer[H1,G1]
  requires H1(x)
  ensures G1(x);
{
			//dprint;
      node tmp = null;
	if (x.next == null)
		x.next = new node(a, tmp);
	else 
		insert(x.next, a);
} 
