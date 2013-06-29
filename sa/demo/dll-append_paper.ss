data node{
	node next;
	node prev;
}

dll<p> == self = null or self::node<x,p> * x::dll<self>;
	
HeapPred G(node a,node b).
HeapPred H(node a,node b).

void dll_append(node x, node y)
infer [H,G] requires H(x,y) ensures G(x,y);
//requires x::dll<p> * y::dll<_> & x!=null &y!=null ensures x::dll<p>;
{
	if (x.next!=null) dll_append(x.next,y);
	else 
		{
			x.next = y;
			y.prev = x;
		}
}
