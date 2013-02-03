HeapPred HP_1(node a).
HeapPred HP_1a(node a).

size_helper:SUCCESS[
ass [H,H1][]:{
  H(x)&x!=null --> x::node<_,p> * HP_1a(p);
  HP_1a(x') --> H(x')&true;
  x::node<_,x'> * H1(x')&true --> H1(x)&true;
  H(x) & x=null --> emp&true;
  emp&x=null --> H1(x)&true
 }

hpdefs [H,H1][]:{
  H1(x) --> H(x);
  H(x) --> x=null or x::node<_,p>*H(p)
 }
]

size:SUCCESS[
ass [H,H1,H2,H3][]:{
   H2(x)&true --> H(x)&true;
   H1(x)&true --> H3(x)&true;
  H1(x)&x!=null --> H3(x)
 }

hpdefs [H2,H3][]:{
   H2(x_594) --> H(x_594);
   H3(x_595) --> H1(x_595)
 }
]
