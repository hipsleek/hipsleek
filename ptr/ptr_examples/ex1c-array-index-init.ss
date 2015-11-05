
data arr {
  int val;
}

/*
data arr_int3 {
  int offset;
  int val;
} inv {self+i}
*/

pred arr_int<o:int,v:int> ==
    p::arr<v> & p=self+o & o>=0
inv o>=0;

void update_arr(arr a,int i,int v)
  requires a::arr_int<i,_>
  ensures  a::arr_int<i,v>;

arr_seg<i:int,n:int> == emp & i>=n & n>=0
  or self::arr_int<i,_> * self::arr_seg<i+1,n>
  inv n>=0 & i>=0;

arr_seg2<i:int,n:int> == emp & i>=n & n>=0
  or self::arr_int<i,5> * self::arr_seg2<i+1,n>
  inv n>=0 & i>=0;

void foo2(arr a,int i)
  requires a::arr_seg<i,10> & i<=10
  ensures a::arr_seg2<i,10>;
{
  if (i<10) {
    update_arr(a,i,5); // a[i] = 5;
    foo2(a,i+1);
  }
}

/*
# ex1c.ss


id: 8; caller: []; line: 35; classic: false; kind: PRE; hec_num: 1; evars: []; impl_vars: [Anon_11]; infer_vars: [ ]; c_heap: emp; others:  es_infer_obj: [] globals: [@dis_err]
 checkentail a::arr_seg<i_1774,flted_31_1775>@M&
v_bool_34_1739' & i'<10 & i_1774=i & i<=10 & flted_31_1775=10 & i'=i & 
a'=a & v_int_35_1732'=5 & MayLoop[]&{FLOW,(4,5)=__norm#E}[]
 |-  (exists i_82: a'::arr_int<i_82,Anon_11>@M&i_82=i'&{FLOW,(4,5)=__norm#E}[]). 
ho_vars: nothing?
res:  failctxfe_kind: MAY
        fe_name: separation entailment
        fe_locs: {
    fc_message: do_unmatched_rhs : p_1788::arr<v_1793>@M(may)
    fc_current_lhs_flow: {FLOW,(4,11)=__MayError#E}
  }
[[ Fold ==>  UnmatchedRHSData]]falseStop z3... 100 invocations 

 */
