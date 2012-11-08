HeapPred HP_2(node a, node b).

get_next[
ass [G4]:{
  x::node<Anon_12,next_24_531'> & x=x' &next_24_531'=null &
  v_node_25_532'=q --> G4(x,x',v_node_25_532',q)

 }

hpdefs [G4]:{
        HP_2(a,b) --> htrue&true;
  G4(x,v_550,res,q) --> x::node<Anon_12,q1>*HP_2(res,q)
  &x=v_550 & res=q & q1=null
 }
]
