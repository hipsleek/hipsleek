HeapPred HP_617(node next_53_563').
HeapPred HP_612(node y_611, node y).
HeapPred HP_581(node next_53_563', node x').
HeapPred HP1(node a, node b).
HeapPred H2(node a, node b).
HeapPred H1b(node a).
HeapPred H1a(node a).
HeapPred H1(node a).
HeapPred G3(node b, node c, node d).
HeapPred G1(node a).
HeapPred G2(node a, node b).

append[
ass [H1,H1a,H1b,G2]: {
 H1a(y) * HP_581(v_node_53_598,x) * x::node<val_53_587,y>&v_node_53_598=null -->  G2(x,y) * H1b(y)&true;
 emp&true -->  H1b(y)&true;
 H1(x)&true -->  x::node<val_53_562',next_53_563'> * HP_581(next_53_563',x)&true;
 HP_581(v_node_53_604,x)&v_node_53_604!=null -->  H1(v_node_53_604)&true;
 H1a(y)&true -->  H1a(y)&true;
 x::node<val_53_589,v_node_53_604> * G2(v_node_53_604,y) * H1b(y)&
v_node_53_604!=null -->  G2(x,y) * H1b(y)&true;
 emp&true -->  H1b(y)&true
}
hpdefs [H1,H1a,H1b,G2]: {
 HP_581(v_node_53_598)&true -->  
 HP_617(next_53_563')&true
 or emp&v_node_53_598=null
 ;
 HP_612(y_611,y)&true -->  
 emp&y_611=y
 or y_611::node<val_53_587,y_615> * HP_612(y_615,y)&true
 ;
 HP_617(next_53_563')&true -->  
 emp&next_53_563'=null
 or next_53_563'::node<val_53_562',next_53_620> * HP_617(next_53_620)&true
 ;
 G2(x,y)&true -->  x::node<val_53_587,y_611> * HP_612(y_611,y)&true;
 H1(x)&true -->  x::node<val_53_562',next_53_563'> * HP_617(next_53_563')&true;
 H1a(y)&true -->  H1b(y)&true;
 H1b(y)&true -->  htrue&true
}
]

