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

G0<x> ==
     self::node<val_29_788,null>@M&self=x 
or x::node<val_29_788,next_29_789> * next_29_789::G5<self> * 
     self::node<val_34_802,null>
inv self!=null;

G5<t> ==
   self=t & self!=null
   or self::node<_,nn>*nn::G5<t>
inv self!=null;

/*
ltwoB<p:node> == HL(p) & self = null  or 
   self::node<_, q> * p::node<_,r> * q::ltwoB<r>;
*/

node foo (node x)
//requires x::ll<> & x!=null ensures res::G0<x>;

infer [H,G]  requires H(x)  ensures  G(x,res);
/*
requires x::ll<> & x!=null
  ensures res::node<_,null> ;
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
# single.ss

This defn for G is incorrect.

 G(next_29_835,t_836) ::=  t_836::node<val_34_802,next_34_803>@M 
  * HP_4(next_34_803,next_29_835) * HP_5(next_29_835,t_836)
   &next_29_835!=null,

We should be using the last two relational assumption instead.
 x::node<val_29_788,null>@M&res=x 
      --> G(x,res)&true,
 x::node<val_29_788,next_29_789>@M * HP_5(next_29_789,res@NI) * 
  res::node<val_34_802,null>@M&next_29_789!=null --> G(x,res)&true]
to derive the defn of post-pred G.

========

[ H(x)&true --> x::node<val_29_788,next_29_789>@M * HP_0(next_29_789)&true,

 HP_0(next_29_789)&next_29_789!=null --> H(next_29_789)&true,

 G(next_29_789,t_32')&
  next_29_789!=null --> t_32'::node<val_34_802,next_34_803>@M * 
  HP_4(next_34_803,next_29_789@NI) * HP_5(next_29_789,t_32'@NI)&true,

 HP_0(next_29_789)&next_29_789=null --> emp&true,

 x::node<val_29_788,null>@M&res=x 
      --> G(x,res)&true,

 x::node<val_29_788,next_29_789>@M * HP_5(next_29_789,res@NI) * 
  res::node<val_34_802,null>@M&next_29_789!=null --> G(x,res)&true]


==========

G(x,res) <->
   x::node<val_29_788,null>@M&res=x 
or x::node<val_29_788,next_29_789>@M * HP_5(next_29_789,res) * 
     res::node<val_34_802,null>

G(next_29_789,t_32')&
  next_29_789!=null --> t_32'::node<val_34_802,next_34_803>@M * 
  HP_4(next_34_803,next_29_789@NI) * HP_5(next_29_789,t_32'@NI)&true,


==========

[ H(x_834) ::=  x_834::node<val_29_788,next_29_789>@M * 
        HP_0(next_29_789),

 HP_0(next_29_837) ::=  
   emp&next_29_837=null
 or next_29_837::node<val_29_788,next_29_789>@M * HP_0(next_29_789)&true

 G(next_29_835,t_836) ::=  t_836::node<val_34_802,next_34_803>@M 
  * HP_4(next_34_803,next_29_835) * HP_5(next_29_835,t_836)
   &next_29_835!=null,

 
 HP_4(next_34_803,next_29_789) ::= NONE]


*/

