data node{
	int val;
	node next;
}

ll<> == self = null  or self::node<_, q> * q::ll<>;

ltwo<p:node> ==  self = null  or self::node<_, q> * p::node<_,r> * q::ltwo<r>;
lthree<p:node,r:node> == r=null & self = null  or self::node<_, q1> * p::node<_,q2> * r::node<_,q3> * q1::lthree<q2,q3>;

HeapPred H(node a, node b).
HeapPred G(node a, node b, node c).

node zip (node x, node y)
infer [H,G]  requires H(x,y)  ensures  G(x,y,res);
//requires x::ltwo<y>  ensures x::lthree<y,res>;
{
   if (x==null) return x;
   else 
   {
   //assume false;
   return new node(x.val+y.val, zip(x.next,y.next));
   }
}
