HeapPred HP_584(node2 a).
HeapPred HP_585(node2 a).
HeapPred HP_595(node2 a).
HeapPred HP_596(node2 a).
HeapPred HP_649(node2 a).
HeapPred HP_650(node2 a).
HeapPred HP_740(node2 a, node2 b).
HeapPred HP_597(node2 b).

delete:SUCCESS[
ass [H1,G1][]:{
 H1(x)&true --> x::node2<val_36_536',prev_36_537',next_36_538'>@M * 
  HP_584(prev_36_537') * HP_585(next_36_538');
 HP_585(v_node2_36_539')&
  true --> v_node2_36_539'::node2<val_36_540',prev_36_541',next_36_542'>@M * 
  HP_595(prev_36_541') * HP_596(next_36_542');
 HP_595(prev_36_610) * HP_596(v_node2_36_622) * 
  v_node2_36_611::node2<val_36_609,prev_36_610,v_node2_36_622>@M&
  v_node2_36_622!=null --> H1(v_node2_36_611)&true;
 HP_596(v_node2_36_622)&
  v_node2_36_622!=null --> v_node2_36_622::node2<val_47_563',prev_47_564',next_47_565'>@M * 
  HP_649(prev_47_564') * HP_650(next_47_565')&true;
 HP_596(v_node2_36_619)&v_node2_36_619=null --> emp&true;
 HP_584(prev_36_594) * x::node2<val_36_593,prev_36_594,next_39_550'>@M&
  next_39_550'=null --> G1(x)&true;
 HP_595(prev_36_604) * res::node2<val_36_603,prev_36_604,v_node2_36_619>@M&
  v_node2_36_619=null --> G2(res)&true;
 HP_584(prev_36_594) * x::node2<val_36_593,prev_36_594,v_node2_36_611>@M * 
  G1(v_node2_36_611)&true --> G1(x)&true;
 G2(res)&true --> G2(res)&true;
 HP_584(prev_36_594) * x::node2<val_36_593,prev_36_594,v_node2_36_622>@M * 
  HP_650(next_47_660) * v_node2_36_622::node2<val_47_659,x,next_47_660>@M&
  true --> G1(x)&true;
 HP_595(prev_36_610) * res::node2<val_36_609,prev_36_610,next_48_569'>@M&
  next_48_569'=null --> G2(res)&true
}

hpdefs [H1,G1][DL_585]:{
   G1(x) --> x::node2<_,DL_585,v_node2_34_612>@M * HP_740(DL_585,v_node2_34_612);
   G2(res) --> res::node2<_,DL_585,next_48_569'>@M & next_48_569'=null;
   H1(x) --> x::node2<_,DL_585,p1>@M * p1::node2<_,DL_585,p2>@M * HP_597(p2);
   HP_740(p1,n) -->
        n::node2<_,DL_585,p>@M * HP_740(DL_585,p)
     or emp&n=null;
   HP_597(n) -->
        n::node2<_,DL_585,p>@M * HP_597(p)&true
     or emp&n=null
 }
]
