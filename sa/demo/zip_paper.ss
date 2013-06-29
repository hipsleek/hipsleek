data node{
	int val;
	node next;
}

ll<> == self = null  or self::node<_, q> * q::ll<>;

ltwo<p:node> == p::ll<> & self = null  or self::node<_, q> * p::node<_,r> * q::ltwo<r>;

HeapPred H(node a, node b).
HeapPred G1(node a, node b, node c).

node zip (node x, node y)
infer [H,G1]  requires H(x,y)  ensures  G1(x,y,res);
//requires x::ltwo<y>  ensures res::ltwo<y> & res=x;
{
   if (x==null) 
	{
		if (y==null) return x;
		else 
		{
			assume false;
			return x;
		}
	}
   else {
     x.val = x.val+y.val;
     x.next = zip(x.next,y.next);
     return x;
   }
}
