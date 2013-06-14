data node{
        int val;
        node prev;
        node next;
}


ll<> == self = null  or self::node<_, _ , q> * q::ll<>;
dll<p> == self = null or self::node<_, p , q> * q::dll<self>;   // p stores the prev node

HeapPred H1(node a, node b).
HeapPred G1(node a, node b).

void paper_fix (node c, node p)
  infer[H1,G1] requires H1(c,p) ensures G1(c,p);
//  requires c::ll<> ensures c::dll<p>;
{
        if (c!=null) 
        {
            c.prev=p;
	        paper_fix(c.next,c); 
        }
}

