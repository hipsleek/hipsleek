HeapPred HP_634(node next_65_555').
HeapPred G3(node a, node b, node c).
HeapPred G2(node a, node b).
HeapPred G1(node a).
HeapPred G(node a, node b).
HeapPred H3(node a, node b, node c).
HeapPred H2(node a, node b).
HeapPred H1(node a).
HeapPred H(node a).

delete1:SUCCESS[
ass [H1,G2][]: {
 H1(x)&x=null & res=null -->  G2(x,res)&true;
 HP_634(next_65_642) * x::node<a',next_65_642>&true -->  G2(x,next_65_642)&true;
 H1(x)&x!=null -->  x::node<val_65_554',next_65_555'> * HP_634(next_65_555')&true;
 HP_634(next_65_644)&true -->  H1(next_65_644)&true;
 x::node<v_int_65_656,next_65_644> * G2(next_65_644,v_node_66_671) * 
v_node_66_567'::node<v_int_65_656,v_node_66_671>&true -->  G2(x,v_node_66_567')&true
}
hpdefs [H1,G2][]: {
 HP_634(next_65_695)&true -->  
 emp&next_65_695=null
 or next_65_695::node<v_int_65_656,v_node_66_687>&v_node_66_687=null
 or next_65_695::node<v_int_65_656,v_node_66_689>&true
 or next_65_695::node<val_65_554',next_65_555'>&next_65_555'=null
 or next_65_695::node<val_65_554',next_65_555'> * 
    next_65_555'::node<a',next_65_555'>&true
 or next_65_695::node<val_65_554',next_65_555'> * 
    next_65_555'::node<v_int_65_656,next_65_690> * 
    next_65_555'::node<v_int_65_656,v_node_66_691>&next_65_690=null
 or next_65_695::node<val_65_554',next_65_555'> * 
    next_65_555'::node<v_int_65_656,next_65_692> * 
    next_65_555'::node<v_int_65_656,v_node_66_693> * 
    next_65_692::node<a',v_node_66_693>&true
 or H1(next_65_695)&true
 ;
 H1(x_694)&true -->  
 emp&x_694=null
 or x_694::node<val_65_674,next_65_555'> * H1(next_65_555')&true
 ;
 G2(x_696,res_697)&true -->  
 emp&res_697=null
 or x_696::node<a',res_697>&true
 or x_696::node<v_int_65_656,next_65_644> * G2(next_65_644,v_node_66_671) * 
    res_697::node<v_int_65_656,v_node_66_671>&true
 
}
]
/*
 6 sim f1:  
 emp&res_697=null & x_696=null
 or x_696::node<a',res_697>&true
 or EXISTS(v_int_65_619: x_696::node<v_int_65_656,next_65_644> * 
    G2(next_65_644,v_node_66_671) * 
    res_697::node<v_int_65_619,v_node_66_671>&v_int_65_619=v_int_65_656&[]
 
 sim f2:  
 emp&res_774=null & x_773=null
 or x_773::node<a',res_774>&true
 or x_773::node<v_int_65_733,next_65_721> * G2(next_65_721,v_node_66_748) * 
    res_774::node<v_int_65_733,v_node_66_748>&true

 emp&res_697=null & x_696=null
 or x_696::node<a',res_697>&true
 or EXISTS(v_int_65_619: x_696::node<v_int_65_656,next_65_644> * 
    G2(next_65_644,v_node_66_671) * 
    res_697::node<v_int_65_619,v_node_66_671>&v_int_65_619=v_int_65_656&[]
 
 f2:  
 emp&res_774=null & x_773=null
 or x_773::node<a',res_774>&true
 or x_773::node<v_int_65_733,next_65_721> * G2(next_65_721,v_node_66_748) * 
    res_774::node<v_int_65_733,v_node_66_748>&true

*/
