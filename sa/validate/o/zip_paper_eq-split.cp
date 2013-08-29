HeapPred HP_936(node y, node@NI x).
HeapPred HP_935(node next_30_934, node@NI y).
HeapPred HP_943(node next_30_942, node@NI x).
HeapPred HP_994(node y).
HeapPred HP_995(node y).
HeapPred HP_996(node y).
HeapPred HP_997(node y).
HeapPred HP_998(node y).

zip:SUCCESS[
ass [H,G][]:{
  // BIND (2;0)
  H(x,y)&y=y' & x!=null --> x::node<val_30_933,next_30_934>@M * HP_935(next_30_934,y) *
     HP_936(y,x),
 // BIND (2;0)
  HP_936(y,x)&x=x' --> y::node<val_30_941,next_30_942>@M * HP_943(next_30_942,x),
 // PRE_REC (2;0)
 HP_935(next_30_934,y) * HP_943(next_30_942,x)&y=y' & x=x' --> H(next_30_934,next_30_942),
 // POST (1;1;0)
 H(res,y)&y=null & x=null & res=null & res=x --> G(x,y,res),
 // POST (2;0)
  x::node<val_30_933,next_30_934>@M * y::node<val_30_941,next_30_942>@M * G(next_30_934,next_30_942,v_node_30_968) *
   res::node<v_int_30_967,v_node_30_968>@M --> G(x,y,res)
 }

hpdefs [H,G][]:{
 G(x_991,y_992,res_993) <-> HP_996(x_991) * HP_997(y_992) * HP_998(res_993),

 H(x_989,y_990) <-> HP_994(x_989) * HP_995(y_990),

 HP_994(self_tmp_infer_1057) <->  emp&self_tmp_infer_1057=null
   or HP_994(next_30_1050) *
    self_tmp_infer_1057::node<val_30_1049,next_30_1050>@M ,

 HP_995(y_1058) <->  emp&y_1058=null
  or HP_995(next_30_1048) * y_1058::node<val_30_1047,next_30_1048>@M ,

 HP_996(self_tmp_infer_1138) <-> emp&self_tmp_infer_1138=null
  or HP_996(next_30_1125) * self_tmp_infer_1138::node<val_30_1123,next_30_1125>@M ,

 HP_997(y_1139) <-> emp&y_1139=null
  or HP_997(next_30_1126) * y_1139::node<val_30_1124,next_30_1126>@M ,

 HP_998(res_1140) <-> emp&res_1140=null
  or HP_998(v_node_30_1128) * res_1140::node<v_int_30_1127,v_node_30_1128>@M

 }
]
