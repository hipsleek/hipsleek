HeapPred HP_1a(node a).
HeapPred HP_1(node a).

#get_size:SUCCESS[
ass [H,G]:{
  x::node<val_25_598,v_node_25_608> * G(v_node_25_608) --> G(x);
  H(x)&x=null --> G(x);
  HP_1a(v_node_25_573') --> H(v_node_25_573');
  H(x)&x!=null --> x::node<val_25_571',next_25_572'> * HP_1a(next_25_572')
 }

hpdefs [H,G]:{
  H(x) --> x=null or x::node<_,p>*H(p);
  G(x) --> x=null or x::node<_,p>*G(p)
 }
]
