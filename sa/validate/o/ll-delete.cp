HeapPred HP_938(node a).
HeapPred GP_972(node a, node b).

whiledel:SUCCESS[
ass [H1,G1][]:{
  // BIND (1;0)
  H1(x)&x!=null --> x::node<val,next>@M * HP_938(next);
 // PRE_REC (1;0)
  HP_938(next)&true --> H1(next);
 // POST (1;0)
  x::node<val,next>@M * G1(next,x')&true --> G1(x,x');
 // POST (2;0)
   H1(x)&x=null & x'=null & x=x' --> G1(x,x')
 }

hpdefs [H1,G1][]:{
   H1(x) <-> x::node<val,next>@M * H1(next) or emp&x=null;
   G1(x1,x) <-> GP_972(x1,x)&x=null;
   GP_972(x1,x) <-> x1::node<val,next>@M * GP_972(next,x)
    or emp&x1=x
 }
]
