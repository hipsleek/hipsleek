HeapPred HP_589(node2 b).
HeapPred HP_590(node2 a).
HeapPred HP_571(node2 a).

search:SUCCESS[
ass [H1,G1][]:{
  H1(x)&x!=null --> x::node2<val_29_532',left_29_533',right_29_534'>@M * HP_589(left_29_533') * HP_590(right_29_534');
  HP_590(right_29_603)&true --> H1(right_29_603)&true;
  HP_589(left_29_602)&true --> H1(left_29_602)&true;
  HP_589(left_29_598) * HP_590(right_29_599) * x::node2<a,left_29_598,right_29_599>@M&true --> G1(x)&true;
  HP_589(left_29_602) * x::node2<v_int_29_611,left_29_602,right_29_603>@M * G1(right_29_603)&true --> G1(x);
  HP_590(right_29_603) * x::node2<v_int_29_611,left_29_602,right_29_603>@M * G1(left_29_602)&true --> G1(x);
  H1(x)&x=null --> emp;
  emp&x=null --> G1(x)&true
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
