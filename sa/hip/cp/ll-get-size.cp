HeapPred HP_2(node a, node b).
HeapPred HP_1(node a).

get_size[
ass [H,G]:{
  x::node<val_25_598,v_node_25_608> * G(v_node_25_608) --> G(x) * HP_2(v_node_25_608,x);
  H(x)&x=null --> G(x);
  HP_2(v_node_25_573',x)&x!=null --> H(v_node_25_573');
  H(x)&x!=null --> x::node<val_25_571',next_25_572'> * HP_2(next_25_572',x)
 }

hpdefs [H,G]:{
  H(x) --> x=null or x::node<_,p>*H(p);
  G(x) --> x=null or x::node<_,p>*G(p)
 }
]
