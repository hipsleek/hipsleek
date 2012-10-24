HeapPred HP_2(node a, node b).
HeapPred HP_1a(node a).
HeapPred HP_1b(node a).

foo[
ass [H,H1]:{
    HP_2(x',x) * x::node<_,x'>&x'=null --> H1(x);
    x::node<_,x'> * H1(x')&x'!=null --> H1(x);
    HP_2(x',x)&x'!=null --> H(x');
    H(x) --> x::node<_,p> * HP_2(p,x)
 }

hpdefs [H,H1]:{
  H1(x) --> x::node<_,p> * HP_1a(p);
  H(x) --> x::node<_,p> * HP_1b(p);
  HP_1a(x) --> x=null or x::node<_,p>*HP_1a(p);
  HP_1b(x) --> x=null or x::node<_,p>*HP_1b(p)
 }
]
