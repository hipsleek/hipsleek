/* trees & binary search trees */
data node{
	node next;
	node prev;
}

dll<p> == self = null or self::node<x,p> * x::dll<self>;

tree<> == self = null or self::node<l,r> * l::tree<> * r::tree<>;

HeapPred H1(node a).
HeapPred H2(node a).
HeapPred Ga (node a, node b).

void append(ref node l1, node l2)
   infer [H1,H2,Ga] requires H1(l1)*H2(l2) ensures Ga(l1,l2);
//	requires l1::dll<p> * l2::dll<_>  ensures l1::dll<p>;
{
	if (l1 == null) 
	{
		l1=l2;
		if (l2!=null) l2.prev = l1;
	}
	else append(l1.next, l2);
}

HeapPred H(node a).
HeapPred G(node a).


/* function to transform a tree in a doubly linked list */
void flatten(node x)
	infer [H,G] requires H(x) ensures G(x); 
	//requires x::tree<> ensures x::dll<null>;
{
	if (x != null)
	{
		flatten(x.next);
		flatten(x.prev);	
		append(x.prev, x.next);
		if (x.prev != null) x.prev.prev = x;
		x.next = x.prev;
		x.prev = null;
	}
}

