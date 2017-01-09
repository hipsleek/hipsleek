HeapPred HP6(node y, node@NI x).
HeapPred HP_935(node next_30_934, node@NI y).
HeapPred HP_943(node next_30_942, node@NI x).

zip:SUCCESS[
ass [H,G][]:{
  // BIND (2;0)
  H(x,y) & x!=null --> x::node<val_30_933,next_30_934>@M * HP6(y,x) * HP_935(next_30_934,y);
 // BIND (2;0)
  HP6(y,x)  --> y::node<val_30_941,next_30_942>@M * HP_943(next_30_942,x);
 // PRE_REC (2;0)
 HP_935(next_30_934,y) * HP_943(next_30_942,x)&y=y' & x=x' --> H(next_30_934,next_30_942);
 // POST (1;1;0)
 H(res,y)&y=null & x=null & res=null & res=x --> G(x,y,res);
 // POST (2;0)
  x::node<val_30_933,next_30_934>@M * y::node<val_30_941,next_30_942>@M * G(next_30_934,next_30_942,v_node_30_968) *
   res::node<v_int_30_967,v_node_30_968>@M --> G(x,y,res)
 }

hpdefs [H,G][]:{
  G(x,y,res_993) <-> emp&y=null & x=null & res_993=null
     or x::node<val_30_933,n_934>@M * y::node<val_30_941,n_942>@M 
       *  res_993::node<v_int_30_967,v_node_30_968>@M * G(n_934,n_942,v_node_30_968);
  H(x_989,y_990) <-> emp&x_989=null & y_990=null
  or y_990::node<val_30_983,n_984>@M *
    x_989::node<val_30_985,n_986>@M * H(n_986,n_984) 

 }
]
