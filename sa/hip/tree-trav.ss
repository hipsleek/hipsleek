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

void to_list(node2 x, node2 tl)
	infer[H,H2]
	requires H(x)*H2(tl)
	ensures H2(x);
/*
requires x::tr<>* tl::ll<_>
ensures x::ll<null>;
*/
{
	if (x !=null)
    {
            if (x.p1!=null) 
			{
				to_list(x.p1,tl);
				if (x.p2!=null)	
				 {
				   to_list(x.p2,x.p1);
				   x.p2.p2 = x;
				   x.p1 = x.p2;
				 }
				else 
				  x.p1.p2 = x;
			}
			else 
			{
				if (x.p2!=null)	
				 {
				   to_list(x.p2,tl);
				   x.p2.p2 = x;
				   x.p1 = x.p2;
				 }
				else 
				{ 
				   x.p1=tl;
				   if (tl!=null) tl.p2 = x;
				}
			}
	x.p2 = null;
    }
}
/*{
        if (x !=null)
        {
                if (x.p1!=null) to_list(x.p1,p);
                else x.p1 = p;
                to_list(x.p2,x.p1);
                if (x.p2!=null)
                        x.p2.p2 = x;
                x.p1 = x.p2;
        }
}*/


/*
int foo(node2 x)
	infer[H] requires H(x) ensures H(x);
{
	if (x != null)	return 1+foo(x.p1)+foo(x.p2);
	else return 0;
}
*/
