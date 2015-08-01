
data str {
  int val;
  str next;
}

DDD<> == self::EEE<> inv true;

EEE<> == self::str<_,_> inv true;

/*
# ex8e4.slk -dre "incr_fixpt_view"

# bug with proc below..

!!! **iast.ml#2142:XXX:0v.view_name:WAITS
!!! **iast.ml#2160:XXX:view:WAIT
!!! **iast.ml#2161:XXX:a:[WAIT]
!!! **iast.ml#2160:XXX:view:memLoc
!!! **iast.ml#2161:XXX:a:[memLoc]
(==astsimp.ml#2575==)
incr_fixpt_view@1
incr_fixpt_view inp1 :[__Exc,__Error,__MayError,__Fail,int_ptr_ptr,int_ptr,lock,barrier,thrd,__RET,__ArrBoundErr,__DivByZeroErr,Object,String,str]
incr_fixpt_view inp2 :[WAITS,WAIT,memLoc,DDD]
incr_fixpt_view@1 EXIT:WAITS

  view_data_name: WAITS

# Why WAITS and not none or unknown?


H_v<v> == self::str<v1,q> * q::H_v<v1> & v!=0
  or self::DDD<> & v=0;

# Why WAITS occur twice?

# ex8e4.ss

!!! **iast.ml#2137:XXX:0v.view_name:WAITS
!!! **iast.ml#2137:XXX:0v.view_name:WAIT
!!! **iast.ml#2137:XXX:0v.view_name:memLoc
!!! **astsimp.ml#2303:XXX:data_name:WAITS
!!! **astsimp.ml#2304:XXX:view_name:WAITS
!!! **astsimp.ml#2303:XXX:data_name:WAIT
!!! **astsimp.ml#2304:XXX:view_name:WAIT
!!! **astsimp.ml#2303:XXX:data_name:memLoc
!!! **astsimp.ml#2304:XXX:view_name:memLoc
!!! **iast.ml#2137:XXX:0v.view_name:WAITS
!!! **iast.ml#2155:XXX:view:WAIT
!!! **iast.ml#2156:XXX:a:[WAIT]
!!! **iast.ml#2155:XXX:view:memLoc
!!! **iast.ml#2156:XXX:a:[memLoc]
!!! **astsimp.ml#2303:XXX:data_name:WAITS
!!! **astsimp.ml#2304:XXX:view_name:DDD

# ex8e4a.ss

!!! **iast.ml#2137:XXX:0v.view_name:WAITS
!!! **iast.ml#2137:XXX:0v.view_name:WAIT
!!! **iast.ml#2137:XXX:0v.view_name:memLoc
!!! **iast.ml#2155:XXX:view:DDD
!!! **iast.ml#2156:XXX:a:[str]
!!! **astsimp.ml#2303:XXX:data_name:WAITS
!!! **astsimp.ml#2304:XXX:view_name:WAITS
!!! **astsimp.ml#2303:XXX:data_name:WAIT
!!! **astsimp.ml#2304:XXX:view_name:WAIT
!!! **astsimp.ml#2303:XXX:data_name:memLoc
!!! **astsimp.ml#2304:XXX:view_name:memLoc
!!! **astsimp.ml#2303:XXX:data_name:str
!!! **astsimp.ml#2304:XXX:view_name:DDD


*/


/*

 view DDD{}[]<>= 
  view_domains: 
   view DDD<>= 
    EBase 
      (* lbl: *){218}->htrue&{FLOW,(1,28)=__flow#E}[]
  view vars: 
  ann vars (0 - not a posn): 
  cont vars: 
  inv: true
  
  baga over inv: [([], true)]
  baga over inv (unfolded): [([], true)]
  
  inv_lock: None
  unstructured formula: (* lbl: *){218}->htrue&{FLOW,(1,28)=__flow#E}[]
  xform: true
  is_recursive?: false
  is_primitive?: false
  is_touching?: false
  is_segmented?: false
  is_tail_recursive?: false
  residents: 
  forward_ptrs: 
  backward_ptrs: 
  forward_fields: 
  backward_fields: 
  same_xpure?: YES
  view_data_name: WAITS
  self preds: []
  materialized vars: []
  addr vars: 
  uni_vars: []
  bag of addr: 
  view_complex_inv: None
  prune branches: ,[]
  prune conditions: 
    {
[]}
  prune baga conditions: 
  prune invs:0:,[]
*/
