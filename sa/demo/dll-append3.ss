data node{
	node next;
	node prev;
}

//dll<p> == self = null or self::node<x,p> * x::dll<self>;
	
HeapPred G(node a,node b).
HeapPred H(node a,node b).

void dll_append(node l1, node l2)
infer [H,G] requires H(l1,l2) ensures G(l1,l2);
//requires l1::dll<p> * l2::dll<_> & l1!=null & l2!=null  ensures l1::dll<p>;

{
	if (l1.next!=null)
		dll_append(l1.next,l2);
	else 
		{
			l1.next = l2;
			l2.prev = l1;
		}
}
/*
!!! >>>>>> mismatch ptr is not found (or inst) in the lhs <<<<<<
( [(,1 ); (,1 )]) :dll-append3.ss:22: 3: bind: node  l2'::node<next_22_776',prev_22_777'>@M[Orig] cannot be derived from context
*/