data arrI {
  int val;
}

arr_seg<i,n> == i=n & i>=0
  or x::arrI<_>*self::arr_seg<i+1,n> & x=self+i & i>=0
  inv n>=i & i>=0;

arr_seg_zero<i,n> == i=n & i>=0
  or x::arrI<0>*self::arr_seg_zero<i+1,n> & x=self+i & i>=0
  inv n>=i & i>=0;

void upd_arr(arrI a, int v)
  requires a::arrI<_>
  ensures a::arrI<v>;

arrI arr_inc(arrI a)
  requires true //a::arrI<_>@L
  ensures  res=a+1;

int get_arr(arrI a)
  requires a::arrI<v>@L
  ensures res=v;

// can base be monomorphic recursive?
void init2(arrI a,int i,arrI base)
  requires base::arr_seg<i,m> & a=base+i & m=10 & 0<=i & i<=m
  ensures  base::arr_seg_zero<i,m>;
{
  if (i<10) {
    upd_arr(a,0);
    i=i+1;
    a = arr_inc(a);
    init2(a,i,base);
  }
}


/*
ex6a.ss (due to incomplete same_base computation)

# can base be monomorphic recursive?

void init2(arrI a,int i,arrI base)
  requires base::arr_seg<i,m> & a=base+i & m=10 & 0<=i & i<=m
  ensures  base::arr_seg_zero<i,m>;
{

# pre-cond fail? even after unfold?

 checkentail base::arr_seg<i_1732,m>@M&
v_bool_35_1690' & i'<10 & i_1732=i & i<=m & 0<=i & m=10 & a=i+base & 
base'=base & i'=i & a'=a & v_int_36_1682'=0 & MayLoop[]&
{FLOW,(4,5)=__norm#E}[]
 |-  a'::arrI<Anon_12>@M&{FLOW,(4,5)=__norm#E}[]. 
ho_vars: nothing?
res:  failctxfe_kind: MAY
        fe_name: separation entailment
        fe_locs: {
    fc_message: do_unmatched_rhs : a'::arrI<Anon_12>@M(may)
    fc_current_lhs_flow: {FLOW,(4,11)=__MayError#E}
  }
[[ Unfold 0 ==>  UnmatchedRHSData]]falseStop z3... 92 invocations 

*/
