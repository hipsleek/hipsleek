data arrI {
  int val;
}

arr_seg<i,n> == i=n & i>=0
  or x::arrI<_>*self::arr_seg<i+1,n> & x=self+i & i>=0
  inv n>=i & i>=0;

arr_seg_sorted<i,n,mi> == x::arrI<mi> & x=self+i & i=n-1 & i>=0
  or x::arrI<mi>*self::arr_seg_sorted<i+1,n,m2> & x=self+i 
       & i>=0 & i<n-1 & mi<=m2
  inv n>i & i>=0;

void upd_arr(arrI base, int i, int v)
  requires a::arrI<_> & a=base+i & i>=0
  ensures a::arrI<v>;

arrI arr_inc(arrI a)
  requires true //a::arrI<_>@L
  ensures res=a+1;

int get_arr(arrI base, int i)
  requires a::arrI<v>@L & a=base+i
  ensures res=v;

void upd_arr_ptr(arrI a, int v)
  requires a::arrI<_>
  ensures a::arrI<v>;

arrI arr_inc_ptr(arrI a)
  requires true //a::arrI<_>@L
  ensures res=a+1;

int get_arr_ptr(arrI a)
  requires a::arrI<v>@L
  ensures res=v;

// can base be monomorphic recursive?
void insert(arrI base,int i,int m,int v)
 requires a::arrI<_> & i>=0 & a=base+i
 case {
   i+1=m -> ensures_exact  base::arr_seg_sorted<i,m,v>;
   i+1!=m  ->
        requires base::arr_seg_sorted<i+1,m,mi>  
        ensures_exact  base::arr_seg_sorted<i,m,min(v,mi)>;
  }
{
  if ((i+1)==m) { 
    //assume false;
    upd_arr(base,i,v);
  } else {
    int k = get_arr(base,i+1);
    if (v<=k) {
        //assume false;
        upd_arr(base,i,v);
    }
    else {
      //assume false;
      upd_arr(base,i,k);
      insert(base,i+1,m,v);
    }
  }
}

/*
# ex6d5.ss 

# fail in post-cond proving..

id: 64; caller: []; line: 45; classic: false; kind: POST; hec_num: 1; evars: []; impl_vars: []; infer_vars: [ ]; c_heap: emp; others:  es_infer_obj: [] globals: [@flow,@ver_post]
 checkentail x_2205::arrI<mi_2202>@M * 
 base::arr_seg_sorted<flted_10_2204,n_2203,m2_2206>@M * a_2220::arrI<v'>@M&
a!=null & Anon_12=Anon_14 & a_2220=a & v'<=v_2165 & v_2165=mi_2202 & 
a_2164=x_2205 & flted_10_2204=1+flted_44_2145 & x_2205=flted_44_2145+base & 
0<=flted_44_2145 & (flted_44_2145+1)<m_2144 & mi<=m2_2206 & mi_2202=mi & 
n_2203=m_2144 & !(v_bool_48_2001') & m_2144=m & flted_44_2145=1+i & 
(1+i)!=m & a=i+base & 0<=i & v'=v & m'=m & i'=i & base'=base & (1+i')!=m' & 
v_bool_53_2000' & MayLoop[]&{FLOW,(4,5)=__norm#E}[]
 |-  (exists i_121,m_122,
flted_45_118: base::arr_seg_sorted<i_121,m_122,flted_45_118>@M&
flted_45_118=min(v,mi) & i_121=i & m_122=m&{FLOW,(4,5)=__norm#E}[]). 
ho_vars: nothing?
res:  failctxfe_kind: MAY
        fe_name: separation entailment
        fe_locs: {
    fc_message: base_case_unfold failed
    fc_current_lhs_flow: {FLOW,(4,5)=__norm#E}
  }


*/
