HeapPred HP_542(node2 a).
HeapPred HP_549(node2 a).
HeapPred HP_1(node2 a).

delete:SUCCESS[
ass [H1,G1][]:{
  H1(x)&true --> x::node2<val_26_520',next_26_521'>@M * HP_542(next_26_521');
 HP_542(p) --> p::node2<val_26_523',next_26_524'>@M * HP_549(next_26_524');
 HP_549(p) * v_node2_26_560::node2<val_26_559,p>@M& p!=null --> H1(v_node2_26_560);
 HP_549(v_node2_26_568)&v_node2_26_568=null --> emp&true;
 x::node2<val_26_548,next_28_528'>@M&next_28_528'=null --> G1(x);
 x::node2<val_26_548,v_node2_26_560>@M * G1(v_node2_26_560)&true --> G1(x)
}

hpdefs [H1,G1,G2][]:{
   H1(x) --> x::node2<_,n>@M * n::node2<_,p> * HP_1(p);
   G1(x) --> x::node2<_,next_33_538'>@M * HP_1(next_33_538');
   HP_1(x) --> x=null or x::node2<_,p>*HP_1(p)
 }
]
]
