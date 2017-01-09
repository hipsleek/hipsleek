HeapPred HP_883(node b).
HeapPred HP_884(node a).
HeapPred HP_891(node b).
HeapPred HP_892(node a).

trav:SUCCESS[
ass [H,G][]:{
 // BIND (1;1;0)
  H(x)&x!=null --> x::node<left_25_881,right_25_882>@M * HP_883(left_25_881) * HP_884(right_25_882);
 // BIND (2;1;0)
  H(x)&x!=null --> x::node<left_26_889,right_26_890>@M * HP_891(left_26_889) * HP_892(right_26_890);
 // PRE_REC (1;1;0)
  HP_883(left_25_881) --> H(left_25_881);
 // PRE_REC (2;1;0)
  HP_892(right_26_890) --> H(right_26_890);
 // POST (1;1;0)
  HP_884(right_25_882) * x::node<left_25_881,right_25_882>@M *G(left_25_881) --> G(x);
 // POST (2;1;0)
  HP_891(left_26_889) * x::node<left_26_889,right_26_890>@M *G(right_26_890) --> G(x);
 // POST (2;0)
  H(x)& x=null --> G(x)
 }

hpdefs [H,G][]:{
  G(z) <-> H(z);
  H(z_609) <-> z_609 = null or z_609::node<l, r> * H(l) * H(r)

 }
]

