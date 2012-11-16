HeapPred HP_587(node a).
HeapPred HP_582(node a).
HeapPred HP_1(node a).
HeapPred HP_682(node a, node b).

trav:SUCCESS[
ass [H1,G2][]:{
     G2(v_node_70_627,v_node_68_606) * x::node<val_68_595,v_node_70_627>&v_node_71_568'=x &  v_node_68_606!=null
          -->  G2(v_node_71_568',x);
     HP_587(v_node_68_623) * x::node<val_68_593,v_node_68_623>& v_node_68_561'=x & v_node_68_623=null
          --> G2(v_node_68_561',x);
     HP_582(v_node_66_557') * x::node<val_66_619,v_node_66_557'>&true --> G2(v_node_66_557',x);
     HP_587(v_node_68_606)& v_node_68_606!=null --> H1(v_node_68_606);
     H1(x)&true --> x::node<val_68_558',next_68_559'> * HP_587(next_68_559');
     H1(x)&true --> x::node<val_66_555',next_66_556'> * HP_582(next_66_556')
 }

hpdefs [H1,G2][]:{
    HP_1(x) --> x=null or x::node<_,p> * HP_1(p);
    HP_682(x,_) --> emp&x=null
         or x::node<_,p> * HP_682(p,_);
    G2(res,x) --> res::node<_,p> * HP_682(p,x);
    H1(x) --> x::node<_,p> * HP_1(p)
 }
]
