HeapPred HP_585(node2 a).
HeapPred HP_586(node2 a).
HeapPred HP_596(node2 a).
HeapPred HP_597(node2 a).
HeapPred HP_645(node2 a).
HeapPred HP_646(node2 a).
HeapPred HP_740(node2 a, node2 b).
HeapPred HP_597(node2 b).

delete:SUCCESS[
ass [H1,G1][]:{
 H1(x) --> x::node2<_,prev_34_545',next_34_546'>@M * HP_585(prev_34_545') * HP_586(next_34_546')&true;
 HP_586(v_node2_34_547') --> v_node2_34_547'::node2<val_34_548',prev_34_549',next_34_550'>@M * 
  HP_596(prev_34_549') * HP_597(next_34_550');
 HP_596(prev_34_611) * HP_597(v_node2_34_623) * 
  v_node2_34_612::node2<val_34_610,prev_34_611,v_node2_34_623>@M&
  v_node2_34_623!=null --> H1(v_node2_34_612)&true;
 HP_597(v_node2_34_623)&
  v_node2_34_623!=null --> v_node2_34_623::node2<val_47_569',prev_47_570',next_47_571'>@M * 
  HP_645(prev_47_570') * HP_646(next_47_571');
 HP_597(v_node2_34_620)&v_node2_34_620=null --> emp&true;
 HP_585(prev_34_595) * x::node2<val_34_594,prev_34_595,next_36_555'>@M&
  next_36_555'=null --> G1(x)&true;
 HP_585(prev_34_595) * x::node2<val_34_594,prev_34_595,v_node2_34_612>@M * 
  G1(v_node2_34_612)&true --> G1(x)&true;
 HP_585(prev_34_595) * x::node2<val_34_594,prev_34_595,v_node2_34_623>@M * 
  HP_646(next_47_656) * v_node2_34_623::node2<val_47_655,x,next_47_656>@M&
  true --> G1(x)&true
}

hpdefs [H1,G1][DL_585]:{
   G1(x) --> x::node2<_,DL_585,v_node2_34_612>@M * HP_740(DL_585,v_node2_34_612);
   H1(x) --> x::node2<_,DL_585,p1>@M * p1::node2<_,DL_585,p2>@M * HP_597(p2);
   HP_740(p1,n) -->
        n::node2<_,DL_585,p>@M * HP_740(DL_585,p)
     or emp&n=null;
   HP_597(n) -->
        n::node2<_,DL_585,p>@M * HP_597(p)&true
     or emp&n=null
 }
]
