HeapPred HP_582(node b).
HeapPred HP_606(node a).

#delete_list:SUCCESS[
ass [D,E]:{
   D(x)&x=null & v_597 = null--> E(x,v_597);
   E(v_node_19_594,v_node_19_595) * x::node<_,v_node_19_594>&x'=null --> E(x,x');
   HP_582(v_node_19_534') --> D(v_node_19_534');
   D(x)&x!=null --> x::node<_,next_19_533'> * HP_582(next_19_533')

 }

hpdefs [D,E]:{
  E(x,v) -->
     x=null & x=v
   or x::node<_,p> * E(p,_)& v=null;
  D(x) --> x=null or x::node<_,p>*D(p)

 }
]
