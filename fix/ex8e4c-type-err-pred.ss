
data str {
  int val;
  str next;
}


pred_prim EEE<> inv true;

HHH<> == self::EEE<> 
  or self::str<_,_> inv true;


/*
# ex8e4c.ss

ERROR: at _0:0_0:0
Message: Can not find flow of str

ERROR: at ex8e4a-verify-shape.ss_23:7_23:16
Message: gather_type_info_var : unexpected exception Failure("Can not find flow of str")


HHH{}[]<> == 

(None,[]): EBase: [][](emp ; (emp ; (self::EEE{}<>@M[HeapNode1]))) * ([] & true)( FLOW __flow) 
||
(None,[]): EBase: [][](emp ; (emp ; (self::str{}<Anon_12,Anon_13>@M[HeapNode1]))) * ([] & true)( FLOW __flow)  inv true inv_lock: None view_data_name:  view_imm_map: []

EEE{}[]<> == EBase: [][](emp ; (emp ; emp)) * ([] & true)( FLOW __flow)  inv true inv_lock: None view_data_name:  view_imm_map: []


*/


