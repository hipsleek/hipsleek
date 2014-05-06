HeapPred HP_947(node a, node@NI b).
HeapPred HP_949(node a, node@NI b).
HeapPred HP_948(node a, node@NI b).
HeapPred HP_971(node a, node@NI b).
HeapPred HP_972(node a, node@NI b).
HeapPred HP_1042(node a).
HeapPred GP_1048(node a, node b).

dll_append:SUCCESS[
ass [H,G][]:{
  // BIND (0)
 H(x,y)&true --> HP_947(prev,y) * HP_949(y,x) * x::node<prev,next>@M * HP_948(next,y) & true;
 // PRE_REC (1;0)
 HP_949(y,x) * HP_948(next,y)&next!=null --> H(next,y);
 // BIND (2;0)
 HP_949(y,x)&true --> y::node<prev,next>@M * HP_971(prev,x) * HP_972(next,x);
 // POST (1;0)
 x::node<prev,next>@M * HP_947(prev,y) * G(next,y)& next!=null --> G(x,y);
 // POST (2;0)
 HP_947(prev,y) * y::node<x,next>@M * x::node<prev,y>@M * HP_972(next,x)&true --> G(x,y);
 // POST (2;0)
 HP_948(next,y)&next=null --> emp&true
}

//__DP_HP_962,__DP_HP_986,__DP_HP_987
hpdefs [H,G][]:{
   H(x,y) <-> x::node<DP2,next>@M * HP_1042(next) * y::node<DP1,DP>;
   G(x1,y) <-> GP_1048(x1,x) * x::node<DP1,y>@M * y::node<x,DP>@M;
   GP_1048(x1,x) <-> x1::node<DP,next>@M * GP_1048(next,x)&next!=null
       or emp&x=x1;
   HP_1042(next) <->  next::node<DP,next1>@M * HP_1042(next1)
    or emp&next=null
 }
]