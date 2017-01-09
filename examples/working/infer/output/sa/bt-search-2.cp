HeapPred HP_901(node2 b).
HeapPred HP_902(node2 a).
HeapPred HP_571(node2 a).

search:SUCCESS[
ass [H1,G1][]:{
 // BIND (1;0)
  H1(x)&x!=null --> x::node2<val_29_898,left_29_899,right_29_900>@M * HP_901(left_29_899) * HP_902(right_29_900);
 // PRE_REC (1;2;1;0)
  HP_902(right_29_900) --> H1(right_29_900);
 // PRE_REC (2;2;1;0)
  HP_901(left_29_899) --> H1(left_29_899);
 // POST (1;1;0)
  HP_901(left_29_899) * HP_902(right_29_900) * x::node2<val_29_898,left_29_899,right_29_900>@M --> G1(x);
 // POST (1;2;1;0)
  HP_901(left_29_899) * x::node2<val_29_898,left_29_899,right_29_900>@M * G1(right_29_900) --> G1(x);
 // POST (2;2;1;0)
  HP_902(right_29_900) * x::node2<val_29_898,left_29_899,right_29_900>@M * G1(left_29_899) --> G1(x);
 // POST (2;0)
  H1(x)& x=null --> G1(x)
 }

hpdefs [H1,G1][]:{
  G1(z) <-> H1(z);
  H1(z_609) <-> z_609 = null or z_609::node2<_, l, r> * H1(l) * H1(r)

 }
]

