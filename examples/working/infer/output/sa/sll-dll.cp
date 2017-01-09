HeapPred HP_893(node a, node b).
HeapPred HP_894(node a, node b).

paper_fix:SUCCESS[
ass [H1,G1][]:{
 // BIND (1;0)
  H1(x,p)&x!=null --> x::node<prev_21_891,next_21_892>@M * HP_893(prev_21_891,p) *
    HP_894(next_21_892,p);
 // PRE_REC (1;0)
  HP_894(next_21_892,p) |#| x'::node<p,next_21_892>@M --> H1(next_21_892,x');
 // POST (1;0)
  x::node<p,next_21_892>@M * G1(next_21_892,x) --> G1(x,p);
 // POST (2;0)
  H1(x,p) & x=null --> G1(x,p)
  }

hpdefs [H1,G1][]:{
 G1(x,p) <-> x::dll<p>;

 H1(x,p_912) <-> x::ll<>
 }
]