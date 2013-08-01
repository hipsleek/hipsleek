HeapPred HP_548(node a).
HeapPred HP_1(node a).
HeapPred HP_617(node a).

insert:SUCCESS[
ass [H1,G1][]:{
  H1(x) --> x::node<val_24_527',next_24_528'>@M * HP_548(next_24_528');
  HP_548(v_node_24_569)&v_node_24_569!=null --> H1(v_node_24_569);
  HP_548(v_node_24_563)&v_node_24_563=null --> emp&true;
  v_node_25_577::node<a,tmp_27'>@M * x::node<val_24_553,v_node_25_577>@M&
  tmp_27'=null --> G1(x);
  x::node<val_24_555,v_node_24_569>@M * G1(v_node_24_569)&
  v_node_24_569!=null --> G1(x)&true
}

hpdefs [H1,G1][]:{
   H1(x) --> x::node<_,p>*HP_1(p);
   G1(x) --> x::node<_,p>*HP_1(p);
   HP_1(x) --> x=null or x::node<_,p1> * HP_1(p1)
 }
]
