data node{
	int val;
	node next;
}

//ll<> == self = null  or self::node<_, q> * q::ll<>;


HeapPred HL(node a).
HeapPred H(node a, node b).
HeapPred G1(node a, node b, node c).

twosame<p:node> == self = null & p=null  or 
   self::node<_, q> * p::node<_,r> * q::twosame<r>;

void error()
 requires true
 ensures false;

node zip (node x, node y)
infer [H,G1]  requires H(x,y)  ensures  G1(x,y,res);
//requires x::twosame<y> ensures x::twosame<y> & res=x;
{
   if (x==null) {
      if (y!=null) error();
      return x;
   }
   else {
     x.val = x.val+y.val;
     x.next = zip(x.next,y.next);
     return x;
   }
}

/*

# zip-same.ss

Small issue: why didn't the elm of redundant pure condition
eliminate !((x_897=null & x_897=y_898).  FIXED

Did we not use xpure proving to eliminate it prior to
forming defn for predicate?


[ H(x_897,y_898) ::=  
 emp&x_897=null & x_897=y_898
 or H(next_29_880,next_29_878) * y_898::node<val_29_877,next_29_878>@M * 
    x_897::node<val_29_879,next_29_880>@M&!((x_897=null & x_897=y_898))

=======

[ H(x,y)&x!=null --> x::node<val_29_821,next_29_822>@M * 
  HP_823(next_29_822,y@NI) * HP_824(y,x@NI)&true,

 HP_824(y,x@NI)&true --> y::node<val_29_828,next_29_829>@M * 
  HP_830(next_29_829,x@NI)&true,

 HP_823(next_29_822,y@NI) * HP_830(next_29_829,x@NI)&
  true --> H(next_29_822,next_29_829)&true,

 H(x,y)&x=null & x=y --> emp&true,

 emp&res=x & x=null & y=null & res=null & res=y & x=y --> G1(x,y,res)&true,

 y::node<val_29_828,next_29_829>@M * 
  G1(next_29_822,next_29_829,v_node_30_860) * 
  x::node<v_int_29_844,v_node_30_860>@M&res=x --> G1(x,y,res)&true]


=================

[ H(x_897,y_898) ::=  
 emp&x_897=null & x_897=y_898
 or H(next_29_880,next_29_878) * y_898::node<val_29_877,next_29_878>@M * 
    x_897::node<val_29_879,next_29_880>@M&!((x_897=null & x_897=y_898))
 ,
 G1(x_899,y_900,res_901) ::=  
 emp&res_901=x_899 & x_899=null & y_900=null & res_901=null & 
 res_901=y_900 & x_899=y_900
 or y_900::node<val_29_828,next_29_829>@M * 
    G1(v_node_30_860,next_29_829,v_node_30_860) * 
    res_901::node<v_int_29_844,v_node_30_860>@M&res_901=x_899
 ,
 HP_823(next_29_822,y) * 
  HP_830(next_29_829,x) ::=  H(next_29_822,next_29_829)&true,

 HP_824(y_895,x_896) ::=  y_895::node<val_29_828,next_29_829>@M * HP_830(next_29_829,x_896)&true]


*/

