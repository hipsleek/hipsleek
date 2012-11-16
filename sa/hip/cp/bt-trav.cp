HeapPred HP_560(node2 b).
HeapPred HP_567(node2 a).
HeapPred HP_550(node2 a,node2 b).

#trav:SUCCESS[
ass [H1,G1]:{
  H1(x)&x=null --> G1(x)&true;
  x::node2<val_26_558,v_node2_26_565,right_26_559> * 
     G1(v_node2_26_565) * G1(right_26_559)&true --> G1(x)&true;
  HP_560(right_26_559)&true --> H1(right_26_559)&true;
  HP_550(v_node2_26_530',right_26_559)&
     true --> H1(v_node2_26_530') * HP_560(right_26_559)&true;
  H1(x)&  x!=null --> x::node2<val_26_527',left_26_528',right_26_529'> * 
     HP_550(left_26_528',right_26_529')&true
 }

hpdefs [H1,G1]:{
  H1(z_609) --> z_609 = null or z_609::node2<_, l, r> * H1(l) * H1(r);
  G1(z_608) --> z_608 = null or z_608::node2<_, l, r> * G1(l) * G1(r)

 }
]
