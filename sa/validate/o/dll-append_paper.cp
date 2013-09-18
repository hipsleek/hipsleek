HeapPred HP_962(node a, node b).
HeapPred HP_963(node a, node b).
HeapPred HP_964(node a, node b).
HeapPred HP_986(node a, node b).
HeapPred HP_987(node a, node b).

dll_append:SUCCESS[
ass [H,G][]:{
 // BIND (0)
  H(x,y) --> x::node<prev_15_960,next_15_961>@M * HP_962(prev_15_960,y) * HP_963(next_15_961,y) * HP_964(y,x);
 // PRE_REC (1;0)
  HP_963(next_15_961,y) * HP_964(y,x)& next_15_961!=null --> H(next_15_961,y);
 // BIND (2;0)
  HP_964(y,x) --> y::node<prev_21_984,next_21_985>@M * HP_986(prev_21_984,x) * HP_987(next_21_985,x);
 // POST (1;0)
  HP_962(prev_15_960,y) * x::node<prev_15_960,next_15_961>@M * G(next_15_961,y)& next_15_961!=null --> G(x,y);
 // POST (2;0)
  HP_963(next_15_961,y)& next_15_961=null --> emp;
 // POST (2;0)
  HP_962(prev_15_960,y) * x::node<prev_15_960,y>@M *HP_987(next_21_985,x) *y::node<x,next_21_985>@M --> G(x,y)
  }

hpdefs [H,G][__DP_HP_962,__DP_HP_986,__DP_HP_987]:{
 G(x_1010,y_1011) <-> x_1010::node<__DP_HP_962,y_1011>@M * y_1011::node<x_1010,__DP_HP_987>@M
   or x_1010::node<__DP_HP_962,next_15_961>@M * G(next_15_961,y_1011)& next_15_961!=null;
 H(x_1006,y_1007) <-> y_1007::node<__DP_HP_986,__DP_HP_987>@M *
      x_1006::node<__DP_HP_962,next_15_999>@M * HP_963(next_15_999,y_1007);
 HP_963(next_15_1008,y_1009) <-> next_15_1008::node<__DP_HP_962,next_15_961>@M * HP_963(next_15_961,y_1009)
   or emp&next_15_1008=null
 }
]