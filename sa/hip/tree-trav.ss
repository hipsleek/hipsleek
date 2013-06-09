data node2 {
	int val;
	node2 p1;
	node2 p2; 
}

HeapPred H(node2 a).
HeapPred H2(node2 a).
HeapPred G(node2 a, node2 b).


void to_list(node2 x, node2 p)
	infer[H,G]
	requires H(x)
	ensures G(x,p);
{
        if (x !=null)
        {
                if (x.p1!=null) to_list(x.p1,p);
                else x.p1 = p;
                to_list(x.p2,x.p1);
                if (x.p2!=null)
                        x.p2.p2 = x;
                x.p1 = x.p2;
        }
}



int foo(node2 x)
	infer[H] requires H(x) ensures H(x);
{
	if (x != null)	return 1+foo(x.p1)+foo(x.p2);
	else return 0;
}

