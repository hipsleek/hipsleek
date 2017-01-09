HeapPred HP_563(node2 a).
HeapPred HP_564(node2 a).

trav:SUCCESS[
ass [H1,G1][]:{
  H1(x)&x!=null --> x::node2<val_26_519',left_26_520',right_26_521'>@M * HP_563(left_26_520') * HP_564(right_26_521');
  HP_563(v_node2_26_522')&true --> H1(v_node2_26_522');
 HP_564(right_26_571)&true --> H1(right_26_571);
 x::node2<val_26_570,v_node2_26_576,right_26_571>@M * G1(v_node2_26_576) *  G1(right_26_571)&true --> G1(x)&true;
 H1(x)&x=null --> emp&true;
 emp&x=null --> G1(x)&true
}

hpdefs [H1,G1][]:{
  H1(z_609) --> z_609 = null or z_609::node2<_, l, r> * H1(l) * H1(r);
  G1(z_608) --> H1(z_608)

 }
]
