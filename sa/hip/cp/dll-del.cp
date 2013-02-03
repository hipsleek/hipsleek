HeapPred HP_560(node2 a).
HeapPred HP_559(node2 a).
HeapPred HP_570(node2 a).
HeapPred HP_571(node2 a).
HeapPred HP_643(node2 a, node2 b).
HeapPred HP_651(node2 a, node2 b).

delete:SUCCESS[
ass [H1,G1][]:{
  H1(x) --> x::node2<val_26_533',prev_26_534',next_26_535'>@M * 
    HP_559(prev_26_534') * HP_560(next_26_535');
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
   H1(x_642) --> x_642::node2<_,DL_559,next_26_535'>@M *HP_643(DL_559,next_26_535');
 G1(x_649) --> x_649::node2<val_26_568,DL_559,n>@M * HP_651(DL_559,n);
 HP_643(p,n) --> n::node2<_,DL_559,n1> * HP_643(DL_559,n1)
         or emp&n=null;
 HP_651(p,n) --> n::node2<_,DL_559,n1> * HP_651(DL_559,n1)
         or emp&n=null
 }
]
