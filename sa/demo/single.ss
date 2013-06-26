data node{
	int val;
	node next;
}

ll<> == self = null  or self::node<_, q> * q::ll<>;

/*
ltwo<p:node> == p::ll<> & self = null  or 
   self::node<_, q> * p::node<_,r> * q::ltwo<r>;
*/

HeapPred HL(node a).
HeapPred H(node a).
HeapPred G(node a, node b).

/*
ltwoB<p:node> == HL(p) & self = null  or 
   self::node<_, q> * p::node<_,r> * q::ltwoB<r>;
*/

node foo (node x)
infer [H,G]  requires H(x)  ensures  G(x,res);
/*
requires x::ll<> & x!=null
ensures res::node<_,null>;
*/
{
   node y = x.next;
   if (y==null) return x;
   else {
     //assume false;
     node t = foo(y);
     t.next=null;
     return t;
   }
}

/*

[ H(x)&true --> 
    x::node<val_29_788,next_29_789>@M * HP_790(next_29_789)&true,
 HP_790(next_29_789)&next_29_789!=null --> H(next_29_789)&true,

 G(next_29_789,t_32')&
  next_29_789!=null --> t_32'::node<val_34_802,next_34_803>@M * 
  HP_804(next_34_803,next_29_789@NI) * HP_805(next_29_789,t_32'@NI)&true,

 HP_790(next_29_789)&next_29_789=null --> emp&true,

 x::node<val_29_788,next_29_789>@M&res=x & next_29_789=null 
    --> G(x,res)&true,

 x::node<val_29_788,next_29_789>@M * G(next_29_789,res) * 
  HP_805(next_29_789,res@NI) * res::node<val_34_802,v_null_34_808>@M&
  next_29_789!=null & v_null_34_808=null --> G(x,res)&true]


*/

