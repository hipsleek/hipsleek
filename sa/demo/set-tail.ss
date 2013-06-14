data node{
	int val;
	node prev;
	node next;
}


HeapPred H1(node a,node b).
  HeapPred G1(node a, node b).

  void set_tail (node c,node y)
  infer[H1,G1] 
  requires H1(c,y) 
  ensures G1(c,y);
{
   c.next = y;
}

/*

[ H1(c,y)&true --> c::node<val_16_779,prev_16_780,next_16_781>@M * 
  (HP_782(prev_16_780,y)) * (HP_783(next_16_781,y))&true,
 (HP_782(prev_16_780,y)) * (HP_783(next_16_781,y)) * 
  c::node<val_16_779,prev_16_780,y>@M&true --> G1(c,y)&true]

=============

[ H1(c_795,y_796) ::= c_795::node<val_16_779,prev_16_780,next_16_781>@M&
 XPURE(HP_782(prev_16_780,y_796)) &  XPURE(HP_783(next_16_781,y_796)),
 G1(c_797,y_798) ::= c_797::node<val_16_779,prev_16_780,y_798>@M&
 XPURE(HP_782(prev_16_780,y_798)) &  XPURE(HP_783(next_16_781,y_798))]

============= --sa-inlining

 H1(c_795,y_796) ::= 
    c_795::node<val_16_779,UU_HP_782_UU,UU_HP_783_UU>@M&true,
 G1(c_797,y_798) ::= 
    c_797::node<val_16_779,UU_HP_782_UU,y_798>@M&true]

*/

