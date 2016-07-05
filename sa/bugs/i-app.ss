data node{
	int val;
	node prev;
	node next;
}

ll<> == self = null  or self::node<_, _ , q> * q::ll<>;

HeapPred H1(node a, node b).
HeapPred G1(node a, node b).

void foo (node c, node y)
  infer [H1,G1]
  requires H1(c,y)
  ensures  G1(c,y);
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

Problems:
 (i) Need to get rid of redundant prev fields..
 (ii) Why is there an extra predicate 
       HP_797(?)

[ H1(c,y)&true --> c::node<val_17_753',prev_17_754',next_17_755'>@M * 
  (HP_778(prev_17_754',y)) * (HP_779(next_17_755',y))&true,
 (HP_778(prev_17_790,y)) * (HP_779(t_32',y))&t_32'!=null 
    --> (H1(t_32',y)) * (HP_797(prev_17_790))&true,
                         ^^^^^^^^^^^^^^^^^^^
 c::node<val_17_789,prev_17_790,t_802>@M * (HP_797(prev_17_790)) *
                                           ^^^^^^^^^^^^^^^^^^^^^ 
  (G1(t_802,y))&t_802!=null --> G1(c,y)&true,
 (HP_778(prev_17_786,y)) * (HP_779(next_22_800,y)) * 
  c::node<val_17_785,prev_17_786,y>@M&next_22_800=null --> G1(c,y)&true]


*/

