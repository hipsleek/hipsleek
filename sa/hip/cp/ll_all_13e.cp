HeapPred HP_574(node a).
HeapPred HP_570(node a).
HeapPred HP_1(node a).
HeapPred HP_682(node a, node b).

trav:SUCCESS[
ass [H1,G2][]:{
   H1(x)&true --> x::node<val_66_555',next_66_556'> * HP_570(next_66_556');
   HP_570(v_node_68_606)& v_node_68_606!=null --> H1(v_node_68_606);
   HP_570(res) * x::node<_,res>&true --> G2(res,x);
   HP_570(v_node_68_623) & v_node_68_623=null  --> emp&true;
   x::node<val_68_593,v_node_68_623>& res=x & v_node_68_623=null --> G2(res,x);
   G2(v_node_70_627,v_node_68_606) * x::node<val_68_595,v_node_70_627>&res=x &  v_node_68_606!=null  -->  G2(res,x)

 }

hpdefs [H1,G2][]:{
    HP_1(x) --> x=null or x::node<_,p> * HP_1(p);
    HP_682(p,res) --> emp&res=null & p=res
         or res::node<_,p1> * HP_682(_,p1) & p=res;
    G2(res,x) --> x::node<_,p> * HP_682(p,res);
    H1(x) --> x::node<_,p> * HP_1(p)
 }
]
