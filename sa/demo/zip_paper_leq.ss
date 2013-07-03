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

/*
--sa-en-sp-split performs split during entailment
and generate continuation HP_864(y) for base-case:

[ HP_864(y)&res=x & x=null & res=null --> G(x,y,res),
 H(x,y)&x=null --> HP_864(y),
                   ^^^^^^^^^
 H(x,y)&x!=null --> x::node<val_22_834,next_22_835>@M * 
  HP_836(next_22_835,y@NI) * HP_837(y,x@NI),
 HP_837(y,x@NI) --> y::node<val_22_841,next_22_842>@M * 
  HP_843(next_22_842,x@NI),
 HP_836(next_22_835,y@NI) * 
  HP_843(next_22_842,x@NI) --> H(next_22_835,next_22_842),
 x::node<val_22_834,next_22_835>@M * y::node<val_22_841,next_22_842>@M * 
  G(next_22_835,next_22_842,v_node_22_868) * 
  res::node<v_int_22_867,v_node_22_868>@M&v_int_22_867=val_22_841+
  val_22_834 --> G(x,y,res)]


 */
