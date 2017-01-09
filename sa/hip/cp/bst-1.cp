HeapPred HP_1c(node a).
HeapPred HP_1a(node a).
HeapPred HP_1b(node a).

count:SUCCESS[
ass [H1,G1][]:{
  z::node2<val_28_572,v_node2_28_580,right_28_573> *
     G1(v_node2_28_580) * G1(right_28_573)&true --> G1(z);
  H1(z)&z=null --> G1(z);
  z::node2<val_27_565,v_node2_27_573,right_27_566>*G1(v_node2_27_573) & z!=null&
     -->  H1(right_27_566);
  HP_564(v_node2_28_540',right_28_573) * z::node2<val_28_537',v_node2_28_540',right_28_539'>
      --> H1(v_node2_28_540');
  H1(z)& z!=null --> z::node2<val_28_537',left_28_538',right_28_539'> *
  HP_564(left_28_538',right_28_539');
 }

hpdefs [H1,G1][]:{
  H1(x) --> x::node<_,p> * HP_1a(p);
  H(x) --> x::node<_,p> * HP_1b(p);
  HP_1a(x) --> x=null or x::node<_,p>*HP_1a(p);
  HP_1b(x) --> x=null or x::node<_,p>*HP_1b(p)
 }
]
