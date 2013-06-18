data node{
	int val;
	node next;
}

ll<> == self = null  or self::node<_, q> * q::ll<>;

//ls<p> == self = p  or self::node<_, q> * q::ls<p>;

HeapPred H1(node a, node b).
HeapPred G1(node a, node b).

void foo (node c, node y)
  infer [H1,G1]
  requires H1(c,y)
  ensures  G1(c,y);
/*
  requires c::ll<> * y::ll<> & c!=null
  ensures  c::ll<>;
  requires c::ll<> & c!=null
  ensures  c::ls<y>;
*/
{
   node t = c.next;
   if (t!=null) {
      foo(t,y);
   }
   else {
      c.next=y;
   }
}

/*
# app.ss

Problem with hip invoking shape_infer...

[ H1(c,y)&true --> c::node<val_16_787,next_16_788>@M * 
  (HP_789(next_16_788,y))&true,
 HP_789(next_16_788,y)&next_16_788!=null --> H1(next_16_788,y)&true,
 c::node<val_16_787,next_16_788>@M * (G1(next_16_788,y))&
  next_16_788!=null --> G1(c,y)&true,
 (HP_789(next_16_788,y)) * c::node<val_16_787,y>@M&
  next_16_788=null --> G1(c,y)&true]

Dangling predicate derived is wrong...

[ H1(c_836,y_837) ::= c_836::node<val_16_787,next_16_788>@M
    & XPURE(HP_789(next_16_788,y_837)),
      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 G1(c_838,y_839) ::= c_838::node<val_16_787,y_840>@M * (HP_841(y_840,y_839))&true,
 HP_841(y_840,y_839) ::= 
 emp& XPURE(HP_789(next_16_788,y_839)) & y_839=y_840 & next_16_788=null
 or y_840::node<val_16_787,y_842>@M * (HP_841(y_842,y_839))&true
 ]

However, app.slk is OK it produced the correct result.
How come hip did not invoke shape_infer correctly?


[ H1(c_87,y_88) ::= c_87::node<val_16_751',next_16_752'>@M * (HP_4(next_16_752',y_88))&true,
 HP_4(next_16_89,y_90) ::= 
 emp&next_16_89=null
 or next_16_89::node<val_16_751',next_16_752'>@M * (HP_4(next_16_752',y_90))&
    true
 ,
 G1(c_91,y_92) ::= c_91::node<Anon_11,t>@M * (HP_93(t,y_92))&true,
 HP_93(t,y_92) ::= 
 emp&t=y_92
 or t::node<Anon_11,t_94>@M * (HP_93(t_94,y_92))&true
 ]

*/

