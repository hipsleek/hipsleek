HeapPred HP_579(node2 b).
HeapPred HP_567(node2 a).
HeapPred HP_557(node2 a,node2 b).

count[
ass [H1,G1]:{
  z::node2<val_27_565,v_node2_27_574,right_27_566> * HP_579(v_node2_27_574) * G1(right_27_566)&true --> G1(z)&true;
  H1(z)&z=null --> G1(z);
  HP_567(right_27_566) * G1(v_node2_27_574)& true --> H1(right_27_566) * HP_579(v_node2_27_574)&true;
  HP_557(v_node2_27_533',right_27_566)& true --> H1(v_node2_27_533') * HP_567(right_27_566)&true;
  H1(z)&  z!=null --> z::node2<val_27_530',left_27_531',right_27_532'> * HP_557(left_27_531',right_27_532')
 }

hpdefs [H1,G1]:{
  H1(z_609) --> z_609 = null or z_609::node2<_, l, r> * H1(l) * H1(r);
  G1(z_608) --> z_608 = null or z_608::node2<_, l, r> * G1(l) * G1(r)

 }
]
