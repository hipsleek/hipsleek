HeapPred HP_1038(node a, node b).
HeapPred HP_1039(node a, node b).
HeapPred HP_1040(node a, node b).

set_right:SUCCESS[
ass [H,G][]:{
 // BIND (0)
  H(x,t) --> x::node<left_31_1035,right_31_1036,next_31_1037>@M *
    HP_1038(left_31_1035,t) * HP_1039(right_31_1036,t) *HP_1040(next_31_1037,t);
 // PRE_REC (2;0)
  HP_1039(right_31_1036,t)& right_31_1036!=null --> H(right_31_1036,t);
 // PRE_REC (2;0)
  HP_1038(left_31_1035,t) --> H(left_31_1035,l_47');
 // POST (1;0)
  HP_1038(left_31_1035,t) * HP_1039(right_31_1036,t) * res::node<left_31_1035,right_31_1036,t>@M&right_31_1036=null &
   res=x --> G(x,res,t);
 // POST (2;0)
  HP_1040(next_31_1037,t) * x::node<left_31_1035,right_31_1036,next_31_1037>@M * G(right_31_1036,l_1069,t) * G(left_31_1035,res,l_1069)&
   right_31_1036!=null --> G(x,res,t)
 }

hpdefs [H,G][]:{
   H(x,t) <-> x::tree<>@M;
   G(x,res,t) <-> x::tll<res,t>@M
 }
]