HeapPred HP_2(node a, node b).
HeapPred HP_1(node a).

foo[
ass [H,H1]:{
    H(x)&x=null --> H1(x)&true;
    x::node<val_24_560,x'> * H1(x')&true --> H1(x)&true;
    HP_2(x',x)&x!=null --> H(x')&true;
    H(x)&x!=null --> x::node<val_24_537',next_24_538'> *
  HP_2(next_24_538',x)&true
 }

hpdefs [H,H1]:{
  H1(x) --> x=null or x::node<_,p>*H1(p);
  H(x) --> x=null or x::node<_,p>*H(p)
 }
]
