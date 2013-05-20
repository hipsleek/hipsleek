data node{
	int val;
	node prev;
	node next;
}

HeapPred H1(node a).
HeapPred G1(node a, node b).

node foo (node c)
  infer[H1,G1] 
  requires H1(c) 
  ensures G1(res,c);
{
    return c.next;
}

/*

Why is there a @L?

[ H1(c)&true --> c::node<val_14_743',prev_14_744',next_14_745'>@M * 
  (HP_765(prev_14_744')) * (HP_766(next_14_745'))&true,
 c::node<val_14_770,prev_14_771,res>@L * (HP_765(prev_14_771)) * 
  (HP_766(res))&true --> G1(res,c)&true]

*/

