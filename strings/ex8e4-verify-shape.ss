
data str {
  int val;
  str next;
}

DDD<> == true inv true;

/*
# ex8e4.slk --pcp

  view_data_name: WAITS

# Why WAITS and not none or unknown?


H_v<v> == self::str<v1,q> * q::H_v<v1> & v!=0
  or self::DDD<> & v=0;

# Why WAITS occur twice?

!!! **iast.ml#2137:XXX:0v.view_name:WAITS
!!! **iast.ml#2137:XXX:0v.view_name:WAIT
!!! **iast.ml#2137:XXX:0v.view_name:memLoc
!!! **iast.ml#2137:XXX:0v.view_name:WAITS
!!! **iast.ml#2155:XXX:view:WAIT
!!! **iast.ml#2156:XXX:a:[WAIT]
!!! **iast.ml#2155:XXX:view:memLoc
!!! **iast.ml#2156:XXX:a:[memLoc]

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
