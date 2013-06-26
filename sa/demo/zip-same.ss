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

# zip.ss

 H(x,y)&x!=null --> x::node<val_31_814,next_31_815>@M *
  (HP_816(next_31_815,y@NI)) * (HP_817(y,x@NI))&true,

 HP_817(y,x@NI)&true --> y::node<val_32_821,next_32_822>@M *
  (HP_823(next_32_822,x@NI))&true,

 (HP_816(next_31_815,y@NI)) * (HP_823(next_32_822,x@NI))&
  true --> H(next_31_815,next_32_822)&true,

 H(x,y)&res=x & x=null & res=null --> G1(x,y,res)&true,

 y::node<val_32_821,next_32_822>@M *
  (G1(next_31_815,next_32_822,v_node_34_853)) *
  x::node<v_int_33_837,v_node_34_853>@M&res=x --> G1(x,y,res)&true

4th RelAssume is a candidate for base-case split which
complements the 1st RelAssume.

In this case, we may also use --sa-s-split to capture
y extension in the base-case.

=================

WHY?

[ H(x_945,y_946) ::= emp&x_945=null,
 G1(x_949,y_950,res_951) ::= HP_952(x_949,y_950,res_951)&res_951=x_949,
 HP_952(x_953,y_950,res_951) ::= 
 emp&res_951=null
 or y_950::node<val_32_821,next_32_822>@M * 
    (HP_952(next_31_815,next_32_822,v_node_34_853))&true
 ]

 H(x,y)&x!=null --> x::node<val_31_814,next_31_815>@M * 
  (HP_816(next_31_815,y@NI)) * (HP_817(y,x@NI))&true,
 HP_817(y,x@NI)&true --> y::node<val_32_821,next_32_822>@M * 
  (HP_823(next_32_822,x@NI))&true,
 (HP_816(next_31_815,y@NI)) * (HP_823(next_32_822,x@NI))&
  true --> H(next_31_815,next_32_822)&true,
 H(x,y)&res=x & x=null & res=null --> G1(x,y,res)&true,
 y::node<val_32_821,next_32_822>@M * 
  (G1(next_31_815,next_32_822,v_node_34_853)) * 
  x::node<v_int_33_837,v_node_34_853>@M&res=x --> G1(x,y,res)&true]



===============================================================
# zip.ss

How come below, when its relational assumption
in zip1f.slk gives correct answer?

[ H(x_945,y_946) ::= emp&x_945=null,
 G1(x_949,y_950,res_951) ::= HP_952(x_949,y_950,res_951)&res_951=x_949,
 HP_952(x_953,y_950,res_951) ::= 
 emp&res_951=null
 or y_950::node<val_32_821,next_32_822>@M * 
    (HP_952(next_31_815,next_32_822,v_node_34_853))&true
 ]


*/

