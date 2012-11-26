HeapPred HP_583(node2 b).
HeapPred HP_575(node2 a,node2 b).

count:SUCCESS[
ass [H1,G1][]:{
 H1(z)&z!=null --> z::node2<val_27_524',left_27_525',right_27_526'> *
   HP_575(left_27_525',right_27_526')&true;
 HP_575(v_node2_27_527',right_27_582)&true --> H1(v_node2_27_527') *
   HP_583(right_27_582)&true;
 HP_583(right_27_582)&true --> H1(right_27_582)&true;
 H1(z)&z=null --> emp&true;
 emp&z=null --> G1(z)&true;
 z::node2<val_27_581,v_node2_27_589,right_27_582> * G1(v_node2_27_589) *
  G1(right_27_582)&true --> G1(z)&true
 }

hpdefs [H1,G1][]:{
  H1(z_609) --> z_609 = null or z_609::node2<_, l, r> * H1(l) * H1(r);
  G1(z_608) --> z_608 = null or z_608::node2<_, l, r> * G1(l) * G1(r)

 }
]
