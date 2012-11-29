HeapPred HP_576(node2 a).
HeapPred HP_568(node2 a,node2 b).

trav:SUCCESS[
ass [H1,G1][]:{
 H1(x)&x!=null --> x::node2<val_26_521',left_26_522',right_26_523'> *
   HP_568(left_26_522',right_26_523')&true;
 HP_568(v_node2_26_524',right_26_575)&true --> H1(v_node2_26_524') *
   HP_576(right_26_575)&true;
 HP_576(right_26_575)&true --> H1(right_26_575)&true;
 x::node2<val_26_574,v_node2_26_581,right_26_575> * G1(v_node2_26_581) *
   G1(right_26_575)&true --> G1(x)&true;
 H1(x)&x=null --> emp&true;
 emp&x=null --> G1(x)&true
}

hpdefs [H1,G1][]:{
  H1(z_609) --> z_609 = null or z_609::node2<_, l, r> * H1(l) * H1(r);
  G1(z_608) --> z_608 = null or z_608::node2<_, l, r> * G1(l) * G1(r)

 }
]
