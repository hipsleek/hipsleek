HeapPred HP_1083(node a, int b).

insert:SUCCESS[
ass [H1,G1][]:{
 // BIND (0)
  H1(x,v)&true --> x::node<val,next>@M * HP_1083(next,v)&true;
 // PRE_REC (1;2;2;0)
  HP_1083(next,v)&val<v & next!=null --> H1(next,v)& true;
 // POST (1;1;0)
  x::node<val,next>@M * HP_1083(next,v)&v<=val --> G1(x,v)& true;
 // POST (1;2;2;0)
  x::node<val,xn>@M&val<v --> G1(x,v)& true;
 // POST (1;2;2;0)
  G1(next,v')&val<v' --> emp& true;
 // POST (2;2;2;0)
  x::node<val,tmp>@M * tmp::node<v1,v>@M * HP_1083(next,v1)& val<v1 & next=null & v=null --> G1(x,v1)&true
 }

hpdefs [H1,G1][]:{
  H1(x,v) <-> x::node<val,next>@M * HP_1083(next,v)&x!=null;
 G1(x,v) <-> x::node<val,next>@M&val<v
   or x::node<val,next>@M * next::node<v,v1>@M&val<v & v1=null
   or x::node<val,next>@M * HP_1083(next,v)&v<=val;
 HP_1083(next,v) <->
   next::node<val1,next1>@M * HP_1083(next1,v)&val<v
   or emp&next=null
 }
]
