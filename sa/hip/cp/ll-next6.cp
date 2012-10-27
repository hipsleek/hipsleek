HeapPred HP_2(node a, node b).
HeapPred HP_2a(node a, node b).
HeapPred HP_1a(node a).

get_next[
ass [H1,G4]:{
    HP_2(v_node_31_529',x) * x::node<val_30_547,v_node_31_529'>&true --> G4(v_node_31_529',x,v_548,p)& x=v_548;
    H1(x,q) --> x::node<val_30_527',next_30_528'> * HP_2(next_30_528',x)

 }

hpdefs [H1,G4]:{
       G4(v_node_31_529',x,v_548,p) --> x::node<val_30_547,v_node_31_529'> * HP_1a(v_node_31_529') *
                                    HP_2a(v_node_31_529',p)&x=v_548;
  H1(x,q) --> x::node<val_28_524',p>*HP_1a(p);
  HP_1a(x) --> htrue&true;
  HP_2a(x,y)  --> htrue&true
 }
]
