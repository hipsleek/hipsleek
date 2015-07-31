
data str {
  int val;
  str next;
}

DDD<> == self::str<_,_> inv true;

D1<> == self::D2<> inv true;
D2<> == self::str<_,_> inv true;


E<> == emp inv true;

F1<> == self::F2<> inv true;
F2<> == self::F1<> inv true;

G1<> == self::G2<> 
  or self::str<_,_> inv true;
G2<> == self::G1<> inv true;


H<> == self::E<> 
  or self::str<_,_> inv true;


/*
H_v<v> == self::str<v1,q> * q::H_v<v1> & v!=0
  or self::DDD<> & v=0;
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
