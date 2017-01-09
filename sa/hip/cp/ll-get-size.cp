HeapPred HP_1a(node a).
HeapPred HP_1(node a).

get_size:SUCCESS[
ass [H,G][]:{
 H(x)&x!=null --> x::node<_,p> * HP_1a(p);
 HP_1a(p) --> H(p);
 x::node<val_25_598,v_node_25_608> * G(v_node_25_608) --> G(x);
 H(x) & x=null --> emp&true;
 emp & x=null --> G(x)
}

hpdefs [H,G][]:{
  H(x) --> x=null or x::node<_,p>*H(p);
  G(x) --> H(x)
 }
]
