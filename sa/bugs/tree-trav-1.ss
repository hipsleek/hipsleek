data node2 {
	int val;
	node2 p1;
	node2 p2; 
}

HeapPred H(node2 a).
HeapPred H2(node2 a).
HeapPred G(node2 a, node2 b).

tr<> == self=null or self::node2<_,l,r>* l::tr<> * r::tr<>;

ll<q> == self=null or self::node2<_,r,q>* r::ll<self>;

void bug_list_neq(node2 x, node2 tl)
	infer[H,H2]
	requires H(x)*H2(tl)
	ensures H2(x);
{
    if (x.p2!=null)	
	   bug_list_neq(x.p2,tl);
	else 
	{ 
	   x.p1=tl;
	   if (tl!=null) tl.p2 = x;
	}
	x.p2 = null;
 }

void bug_obtain_xpure(node2 x, node2 tl)
	infer[H,H2]
	requires H(x)*H2(tl)
	ensures H2(x);
{
	   x.p2 = tl.p2;
}
