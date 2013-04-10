HeapPred HP_560(node2 a).
HeapPred HP_559(node2 a).
HeapPred HP_570(node2 a).
HeapPred HP_571(node2 a).
HeapPred HP_643(node2 a, node2 b).
HeapPred HP_630(node2 a, node2 b).

delete:SUCCESS[
ass [H1,G1][]:{
  H1(x) --> x::node2<_,p1,n1>@M * HP_559(p1) * HP_560(n1);
  HP_560(v_node2_26_536') --> v_node2_26_536'::node2<_,p,n>@M * HP_570(p) * HP_571(n);
 HP_570(prev_26_585) * HP_571(v_node2_26_600) * 
  v_node2_26_586::node2<val_26_584,prev_26_585,v_node2_26_600>@M&
  v_node2_26_600!=null --> H1(v_node2_26_586)&true;
 HP_571(v_node2_26_594)&v_node2_26_594=null --> emp&true;
 HP_559(prev_26_569) * x::node2<val_26_568,prev_26_569,next_28_544'>@M&
  next_28_544'=null --> G1(x)&true;
 HP_559(prev_26_569) * x::node2<val_26_568,prev_26_569,v_node2_26_586>@M * 
  G1(v_node2_26_586)&true --> G1(x)&true
}

hpdefs [H1,G1][DL_559]:{
   H1(x) --> x::node2<_,DL_559,n1>@M * n1::node2<_,DL_559,n2>@M * HP_571(n2);
   G1(x) --> x::node2<_,DL_559,n1>@M * HP_630(DL_559,n1);
   HP_630(p,n) -->
        n::node2<_,DL_559,n1>@M * HP_630(DL_559,n1) or n=null;
   HP_571(p) --> p::node2<_,DL_559,n> * HP_571(n) or p=null
 }
]
