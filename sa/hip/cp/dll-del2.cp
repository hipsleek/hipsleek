HeapPred HP_554(node2 a).
HeapPred HP_561(node2 a).
HeapPred HP_1(node2 a).

delete:SUCCESS[
ass [H1,G1,G2][]:{
 H1(x) --> x::node2<val_29_528',next_29_529'>@M * HP_554(next_29_529');
 HP_554(v_node2_29_530') --> v_node2_29_530'::node2<val_29_531',next_29_532'>@M * HP_561(next_29_532');
 HP_561(v_node2_29_591) * v_node2_29_572::node2<val_29_571,v_node2_29_591>@M&
  v_node2_29_591!=null --> H1(v_node2_29_572);
 HP_561(v_node2_29_579)&v_node2_29_579=null --> emp&true;
 x::node2<val_29_560,next_33_538'>@M&next_33_538'=null --> G1(x);
 res::node2<val_29_567,v_node2_29_579>@M&v_node2_29_579=null --> G2(res);
 x::node2<val_29_560,v_node2_29_572>@M * G1(v_node2_29_572)&true --> G1(x);
 G2(res)&true --> G2(res)
}

hpdefs [H1,G1,G2][]:{
   H1(x) --> x::node2<_,n>@M * n::node2<_,next_29_605>@M * HP_1(next_29_605);
   G1(x) --> x::node2<_,next_33_538'>@M * HP_1(next_33_538');
   G2(res) --> res::node2<_,v_node2_29_579>@M&v_node2_29_579=null;
   HP_1(x) --> x=null or x::node2<_,p>*HP_1(p)
 }
]
