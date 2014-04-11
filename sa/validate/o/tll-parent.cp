HeapPred HP_1012(node parent_35_1008, node@NI p, node@NI t).
HeapPred H(node a, node@NI p, node@NI b).
HeapPred HP_1013(node left_35_1009, node@NI p, node@NI t).
HeapPred HP_1014(node right_35_1010, node@NI p, node@NI t).
HeapPred HP_1015(node next_35_1011, node@NI p, node@NI t).
HeapPred G(node a, node@NI p, node@NI b, node@NI c).


set_right:SUCCESS[
ass [H,G][]:{
  // BIND(0)
  H(x,p,t)&true --> x::node<parent,left,right,next>@M * HP_1012(parent,p,t) * HP_1013(left,p,t) *
   HP_1014(right,p,t) * HP_1015(next,p,t)&true;
 // PRE_REC (2;0)
 HP_1014(right,p,t)&right!=null |#| x'::node<p,left,right,next>@M& true --> H(right,x',t)&true;
 // PRE_REC (2;0)
 HP_1013(left,p,t)&true |#| x'::node<p,left,right,next>@M&right!=null --> H(left,x',l')&true;
 // POST (1;0)
 HP_1013(left,p,t) * HP_1014(right,p,t) *res::node<p,left,right,t>@M &
  right=null & res=x --> G(x,p,res,t)&true;
 // POST (2;0)
 HP_1015(next,p,t) * x::node<p,left,right,next>@M * G(right,x,l,t) * G(left,x,res,l)&
  right!=null --> G(x,p,res,t)&true
 }
hpdefs [H,G][]:{
  H(x,p,t) <-> x::tree<>@M;
  G(x,p,res,t) <-> x::tll<p,res,t>
}
]
