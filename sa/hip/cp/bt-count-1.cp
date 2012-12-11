HeapPred HP_570(node2 b).
HeapPred HP_571(node2 a).
HeapPred HP_571(node2 a).
count:SUCCESS[
ass [H1,G1][]:{
  H1(z)&z!=null --> z::node2<val_27_522',left_27_523',right_27_524'> * HP_570(left_27_523') * HP_571(right_27_524');
  HP_570(v_node2_27_525')&true --> H1(v_node2_27_525');
  HP_571(right_27_578)&true --> H1(right_27_578);
  H1(z)&z=null --> emp&true;
  emp&z=null --> G1(z)&true;
  z::node2<val_27_577,v_node2_27_584,right_27_578>@M * G1(v_node2_27_584) * G1(right_27_578)&true --> G1(z)&true
 }

hpdefs [H1,G1][]:{
  H1(z_609) --> z_609 = null or z_609::node2<_, l, r> * H1(l) * H1(r);
  G1(z_608) --> H1(z_608)

 }
]

/*
H1(z)&z!=null --> z::node2<val_27_524',left_27_525',right_27_526'> *  HP_575(left_27_525',right_27_526')&true;
 HP_575(v_node2_27_527',right_27_582)&true --> H1(v_node2_27_527') *   HP_583(right_27_582)&true;
 HP_583(right_27_582)&true --> H1(right_27_582)&true;
 H1(z)&z=null --> emp&true;
 emp&z=null --> G1(z)&true;
 z::node2<val_27_581,v_node2_27_589,right_27_582> * G1(v_node2_27_589) *
  G1(right_27_582)&true --> G1(z)&true
*/
