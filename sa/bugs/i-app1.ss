data node{
	int val;
	node next;
}

ll<> == self = null  or self::node<_, q> * q::ll<>;

HeapPred H1(node a).
HeapPred G1(node a, node b).

void foo (node c, node y)
  infer [H1,G1]
  requires H1(c)
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
 H1(c,y)&true --> c::node<val_16_751',next_16_752'>@M * 
    HP_774(next_16_752',y)&true,
 HP_774(t_31',y)&t_31'!=null --> H1(t_31',y)&true,
 c::node<val_16_781,t_792>@M * G1(t_792,y) &t_792!=null --> G1(c,y)&true,
 HP_774(next_21_790,y) * c::node<val_16_779,y>@M & next_21_790=null --> G1(c,y)&true]

*/

