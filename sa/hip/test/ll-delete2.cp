HeapPred HP_549(node next_19_526').
HeapPred E(node a, node b).
HeapPred D(node a).

delete_list[
ass [D,E]: {
 D(x)&x!=null -->  x::node<val_19_525',next_19_526'> * HP_549(next_19_526')&true;
 HP_549(v_node_19_527')&true -->  D(v_node_19_527')&true;
 E(v_node_19_561,v_node_19_562) * x::node<val_19_555,v_node_19_561>&x'=null -->  E(x,x')&true;
 D(x)&x=null -->  E(x,v_564)&x=v_564
}
hpdefs [D,E]: {
 HP_549(v_node_19_574)&true -->  
 v_node_19_574::node<val_19_525',next_19_568>&next_19_568=null
 or v_node_19_574::node<val_19_525',next_19_526'>&next_19_526'=null
 or v_node_19_574::node<val_19_525',next_19_526'> * 
    next_19_526'::node<val_19_525',next_19_571>&next_19_571=null
 or v_node_19_574::node<val_19_525',next_19_526'>&true
 or emp&v_node_19_574=null
 ;
 E(x_575,x_576)&true -->  
 emp&x_575=x_576 & x_575=null
 or E(v_node_19_561,v_node_19_562) * x_575::node<val_19_555,v_node_19_561>&
    x_576=null
 ;
 D(x_577)&true -->  
 x_577::node<val_19_525',next_19_526'> * D(next_19_526')&true
 or emp&x_577=null
 
}
]

