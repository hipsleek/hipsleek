HeapPred HP_1a(node a).
HeapPred HP_1b(node a).

trav[
ass [H1,G1]:{
 x::node<_,v_node_68_596> * G1(v_node_68_596) --> G1(x) * HP_1b(v_node_68_596);
 H1(x)&x!=null --> G1(x)&true;
 H1(x)&x=null --> G1(x);
 HP_1a(v_node_68_567') --> H1(v_node_68_567');
 H1(x)&x!=null --> x::node<_,next_68_566'> * HP_1a(next_68_566')
 }

hpdefs [G1]:{
       H1(x) --> x=null or x::node<_,p> * H1(p);
     G1(x) --> x=null or x::node<_,p> * G1(p)
 }
]
