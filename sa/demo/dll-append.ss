data node{
	node next;
	node prev;
}

dll<p> == self = null or self::node<x,p> * x::dll<self>;

dllt<p,tl> == self = tl	or self::node<x,p> * x::dllt <self,tl>;
	
HeapPred H1(node a).
HeapPred H2(node a).
HeapPred G(node a, node b).
	
void dll_append(node l1, node l2)
 infer [H1,H2,G] requires H1(l1)*H2(l2) ensures G(l1,l2);
//requires l1::dll<p> * l2::dll<_> & l1!=null  ensures l1::dll<p>;
// requires l1::dllt<p,null> * l2::dll<_> & l1!=null  ensures l1::dll<p>;
{
	if (l1.next!=null)
		dll_append(l1.next,l2);
	else 
		{
			l1.next = l2;
			if (l2!=null) l2.prev = l1;
		}
}

void append(ref node l1, node l2)
   infer [H1,H2,G] requires H1(l1)*H2(l2) ensures G(l1,l2);
//	requires l1::dll<p> * l2::dll<_>  ensures l1::dll<p>;
{
	if (l1 == null) 
	{
		l1=l2;
		if (l2!=null) l2.prev = l1;
	}
	else append(l1.next, l2);
}

