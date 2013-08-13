data node{
	node prev;
	node next;
}


HeapPred H(node a, node@NI b).
PostPred G(node a, node@NI b).

  void set_tail (node x,node y)
 infer[H,G]   requires H(x,y) ensures G(x,y);
//requires x::node<a,_> ensures x::node<a,y>;
{
// node t = x.next;
   x.next = y;
}

/*
# set-tail.ss

option --pred-en-dangling

GOT
===
 H(x_784,y_785) ::=  x_784::node<prev_16_778,next_16_779>@M 
   * H_0(prev_16_778,y_785) * H_1(next_16_779,y_785) 
   * H_2(y_785,x_784),

 G(x_786,y_787) ::=  H_0(prev_16_778,y_787) 
   * H_2(y_787,x_786) * x_786::node<prev_16_778,y_787>@M,

 H_2(y,x) ::= NONE,
 H_0(prev_16_778,y) ::= NONE,
 H_1(next_16_779,y) ::= NONE]

There are three unknown (new dangling) preds. We would like to
remove them from our predicate definition.
  H_2 pred originate from parameter y (parameter dangling)
  H_0/H_1 pred originate from fields next/prev. (field dangling)
You can easily check this on the root paramter of each
pred defn. For parameter dangling, we just remove them
without any other change. However, for each field-dangling,
we would replace its root paramter by a unique name,
e.g. HP_x(field,..) replaced field by __UU_DG_HP_x

EXPECTED
========
 H(x_784,y_785) ::=  x_784::node<__DP_H_0,__DP_H_1>@M 

 G(x_786,y_787) ::=  x_786::node<__DP_H_0,y_787>@M,

============= --sa-inlining

 H1(c_795,y_796) ::= 
    c_795::node<val_16_779,UU_HP_782_UU,UU_HP_783_UU>@M&true,
 G1(c_797,y_798) ::= 
    c_797::node<val_16_779,UU_HP_782_UU,y_798>@M&true]

*/

