HeapPred HP_943(node a).
HeapPred HP_953(node a).
HeapPred HP_954(node a).
HeapPred HP_944(node a).
HeapPred HP_976(node a).
HeapPred HP_977(node a).
HeapPred GP_1048(node a, node b).


dll_append:SUCCESS[
ass [H,G][]:{
  // BIND(0)
  HP_943(x)&true --> x::node<prev,next>@M * HP_953(prev) * HP_954(next);
 // PRE_REC (1;0)
  HP_954(next)&next!=null --> HP_943(next);
 // PRE_REC (1;0)
  HP_944(y)&true --> HP_944(y);
 // BIND (2;0)
  HP_944(y)&true --> y::node<prev,next>@M * HP_976(prev) * HP_977(next);
 // POST (1;0)
  x::node<prev,next>@M * HP_953(prev) * G(next,y)&next!=null --> G(x,y);
 // POST (2;0)
  HP_953(prev) * HP_954(next1) * x::node<prev,y>@M * HP_977(next) * 
      y::node<x,next>@M&next1=null --> G(x,y)
}

//__DP_HP_962,__DP_HP_986,__DP_HP_987
hpdefs [H,G][]:{
   H(x,y) <-> HP_943(x) * HP_944(y);
   HP_943(x) <-> x::node<DP2,next>@M * HP_954(next);
   HP_944(y) <-> y::node<DP1,DP>;
   G(x1,y) <-> GP_1048(x1,x) * x::node<DP1,y>@M * y::node<x,DP>@M;
   GP_1048(x1,x) <-> x1::node<DP,next>@M * GP_1048(next,x)&next!=null
       or emp&x=x1;
   HP_954(next) <->  next::node<DP,next1>@M * HP_954(next1)
    or emp&next=null
 }
]
