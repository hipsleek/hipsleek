HeapPred HP_938(node a, node b).
HeapPred HP_939(node a, node b).
HeapPred HP_940(node a, node b).

set_right:SUCCESS[
ass [H,G][]:{
 // BIND (0)
  H(x,t) --> x::node<left_31_935,right_31_936,next_31_937>@M * HP_938(left_31_935,t) * HP_939(right_31_936,t) *
     HP_940(next_31_937,t);
 // PRE_REC (2;0)
  HP_939(right_31_936,t)& right_31_936!=null --> H(right_31_936,t);
 // PRE_REC (2;0)
  HP_938(left_31_935,t) --> H(left_31_935,l_47');
 // POST (1;0)
  HP_938(left_31_935,t) * HP_939(right_31_936,t) * x::node<left_31_935,right_31_936,t>@M&right_31_936=null &
    res=x --> G(x,res,t);
 // POST (2;0)
  HP_940(next_31_937,t) * x::node<left_31_935,right_31_936,next_31_937>@M * G(right_31_936,l_969,t) *
    G(left_31_935,res,l_969)&right_31_936!=null --> G(x,res,t)
 }

hpdefs [H,G][__DP_HP_962,__DP_HP_960]:{
 G(x_1020,res_1021,t_1022) <-> x_1020::node<left_31_957,right_31_958,__DP_HP_962>@M *
   G(right_31_958,l_991,t_1022) * G(left_31_957,res_1021,l_991)& right_31_958!=null
   or res_1021::node<__DP_HP_960,right_31_958,t_1022>@M&res_1021=x_1020 & right_31_958=null;
 H(x_1017,t_1018) <-> H(left_31_994,l_47') * x_1017::node<left_31_994,right_31_995,next_31_996>@M& right_31_995!=null
   or x_1017::node<__DP_HP_960,right_31_958,__DP_HP_962>@M&right_31_958=null
 }
]