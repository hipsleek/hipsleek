HeapPred HP_2(node a, node b).
HeapPred HP_2a(node a, node b).
HeapPred HP_2b(node a, node b).
HeapPred HP_801(node a, node c).
HeapPred HP_1(node a).

append:SUCCESS[
ass [H2,G2][]:{
   H2(x,y)&x!=null --> x::node<val_35_772',next_35_773'>@M *
  (HP_801(next_35_773',y));
 HP_801(v_node_35_774',y)&true --> H2(v_node_35_774',y);
 H2(x,y)&x=null & res=y --> G2(res,y);
 res::node<val_35_808,v_node_35_817>@M * (G2(v_node_35_817,y))&
  true --> G2(res,y)&true
	}

hpdefs [G2,H2][DLING_HP_605]:{
 G2(x,y) --> HP_2(x,y) & DLING_HP_605=y;
 H2(x,y) --> x::node<_,p>* H2(p,y) or x=null & DLING_HP_605=y;
 HP_2(x,p) --> x=p or x::node<_,p1> * HP_2(p1,p)
 }
]
