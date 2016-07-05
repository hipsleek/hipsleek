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

 H1(c,y)&true --> c::node<val_16_745',prev_16_746',next_16_747'>@M * 
  (HP_766(prev_16_746',y)) * (HP_767(next_16_747',y))&true

 c::node<val_16_771,prev_16_772,y>@M * HP_766(prev_16_772,y) * 
  HP_767(next_16_768,y) & true --> G1(c,y)&true


H1(c_773,y_774) ::= c_773::node<val_16_745',prev_16_746',next_16_747'>@M * 
(HP_766(prev_16_746',y_774)) * (HP_767(next_16_747',y_774))&true,
 
G1(c_775,y_776) ::= (HP_766(prev_16_772,y_776)) 
      * (HP_767(next_16_768,y_776)) 
      * c_775::node<val_16_771,prev_16_772,y_776>@M&true,



*/

