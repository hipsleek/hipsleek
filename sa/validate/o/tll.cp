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

hpdefs [H,G][]:{
 G(x_995,res_996,t_997) <->  HP_940(next_31_937,t_997) * x_995::node<left_31_935,right_31_936,next_31_937>@M *
      G(right_31_936,l_969,t_997) * G(left_31_935,res_996,l_969)& right_31_936!=null
   or x_995::node<left_31_935,right_31_936,t_997>@M * H(left_31_935,l_994)&res_996=x_995 & right_31_936=null;

 H(x_989,t_990) <-> H(left_31_979,l_47') *x_989::node<left_31_979,right_31_980,next_31_981>@M *HP_939(right_31_980,t_990);

 HP_939(right_31_992,t_993) <-> emp&right_31_992=null
   or H(left_31_985,l_47') * right_31_992::node<left_31_985,right_31_986,next_31_984>@M *
     HP_939(right_31_986,t_993);
 HP_940(next_31_937,t) <->htrue
 }
]