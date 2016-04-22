data arrI {
  int val;
}

arr_seg<i,n> == i=n & i>=0
  or x::arrI<_>*self::arr_seg<i+1,n> & x=self+i & i>=0
  inv n>=i & i>=0;

/* arr_seg_sorted<i,n,mi> == x::arrI<mi> & x=self+i & i=n-1 & i>=0 */
/*   or x::arrI<mi>*self::arr_seg_sorted<i+1,n,m2> & x=self+i  */
/*        & i>=0 & i<n-1 & mi<=m2 */
/*   inv n>i & i>=0; */

arr_seg_max<i,n,maxv,pos> == x::arrI<maxv> & x=self+i & i=n-1 & i>=0 & i=pos //& cur<=max_value
  or x::arrI<cur> * self::arr_seg_max<i+1,n,maxv2,_> & x=self+i & i>=0 & i<n-1 & i=pos & maxv=cur & cur>=maxv2
  or x::arrI<cur> * self::arr_seg_max<i+1,n,maxv2,pos> & x=self+i & i>=0 & i<n-1 & !(i=pos) & maxv=max(cur,maxv2)
  inv n>i & i>=0;

/* arr_seg_max_1<i,n,maxv> == i=n & i>=0 //& cur<=max_value */
/*   or x::arrI<maxv> & x=self+i & i=n-1 & i>=0 */
/*   or x::arrI<cur> * self::arr_seg_max_1<i+1,n,maxv2> & x=self+i & i>=0 & i<n & maxv=max(cur,maxv2) & maxv>=cur & maxv>=maxv2 */
/*   inv n>i & i>=0; */

/* arr_seg_max_2<i,n,maxv> == i=n & i>=0 //& cur<=max_value */
/*   or x::arrI<cur> * self::arr_seg_max_2<i+1,n,maxv2> & x=self+i & i>=0 & i<n & maxv=max(cur,maxv2) */
/*   inv n>i & i>=0; */



/* arr_seg_sorted<i,n,ma,mi> == i=n & i>=0 */
/*   or x::arrI<m1> * self::arr_seg_sorted<i+1,n,m2,mi> &  m1>m2 */
/*   or self::arr_seg_sorted<i,n-1,ma,m1> * x::arrI<m2> & m1>m2 */
/*   inv n>i & i>=0; */


/* void merge_max(arrI base,int i, int k, int n, int m) */
/*   requires base::arr_seg_max_2<i,k,m1> * base::arr_seg_max_2<k,n,m2> & m1<=m & m2<=m */
/*   ensures base::arr_seg_max_2<i,n,m>; */

/* void merge_max_simp(arrI base,int i, int k, int n, int m) */
/*   requires base::arr_seg_max_1<i,k,_> * base::arr_seg_max_1<k,n,_> */
/*   ensures base::arr_seg_max_1<i,n,m>; */

/* void reverse_unfold(arrI base, int i,int n,int m) */
/*   requires x::arrI<m1>*base::arr_seg_max_2<i+1,n,m2> & x=base+i & m1<=m & m2<=m */
/*   ensures base::arr_seg_max_2<i,n,m>; */

/* void reverse_unfold_simp(arrI base, int i,int n,int m) */
/*   requires x::arrI<m1>*base::arr_seg_max_2<i+1,n,m2> & x=base+i */
/*   ensures base::arr_seg_max_2<i,n,m>; */

void split_arr(arrI base,int i,int m,int k)
  requires base::arr_seg_max<i,m,v,p> & i<=k & k<m & p=k
  ensures base::arr_seg_max<i,k,v1,_> * base::arr_seg_max<k,m,v,p> & v1<=v;

void merge_arr(arrI base,int i,int m,int k)
  requires base::arr_seg_max<i,k,v1,_> * base::arr_seg_max<k,m,v2,pos> & v1<=v2
  ensures base::arr_seg_max<i,m,v2,pos>;


void unfold_arr(arrI base,int i, int m)
  requires base::arr_seg_max<i,m,v,i>
  ensures  x::arrI<cur> * base::arr_seg_max<i+1,m,maxv2,_> & x=base+i & i>=0 & i<n-1 & cur=v & v=max(cur,maxv2);

void reverse_unfold(arrI base, int i, int m)
  requires x::arrI<v> * base::arr_seg_max<i+1,m,v1,_> & x=base+i & v>=v1
  ensures base::arr_seg_max<i,m,v1,i>;

void reverse_unfold_update(arrI base, int i, int m)
  requires x::arrI<v> * base::arr_seg_max<i+1,m,_,j> & x=base+i
  ensures base::arr_seg_max<i,m,v,i>;
/* void upd_arr(arrI base, int i, int v) */
/*   requires a::arrI<_> & a=base+i & i>=0 */
/*   ensures a::arrI<v> & a=base+i; */

/* arrI arr_inc(arrI a) */
/*   requires true //a::arrI<_>@L */
/*   ensures res=a+1; */

int get_arr(arrI base, int i)
  requires a::arrI<v>@L & a=base+i
  ensures res=v;

int get_max(arrI base,int i,int m)
  requires base::arr_seg<i,m>&i<m // generalization
  ensures  base::arr_seg_max<i,m,_,res>&res>=i&res<m;
{
  if(i==m-1)
    {
      return i;
    }
  else{
    int cur = get_arr(base,i);
    dprint;
    int tmp_index = get_max(base,i+1,m);
    dprint;
    split_arr(base,i+1,m,tmp_index);
    unfold_arr(base,tmp_index,m);
    dprint;
    int tmp = get_arr(base,tmp_index);
    ///   dprint;
    if(tmp<cur)
      {
        assume false;
        reverse_unfold(base,tmp_index,m);
        merge_arr(base,i+1,m,tmp_index);
        return i;
      }
    else
      {
        reverse_unfold(base,tmp_index,m);
        dprint;
        merge_arr(base,i+1,m,tmp_index);
        reverse_unfold(base,i,tmp_index);
        //dprint;
        return tmp_index;
      }
  }
}

/* dprint(simpl): ex6l3-selection-sort.ss:112: ctx:  List of Failesc Context: [FEC(0, 0, 1  [(,1 ); (,2 ); (,1 ); (,2 )])] */
/*  Successful States: */
/*  [ */
/*   Label: [(,1 ); (,2 ); (,1 ); (,2 )] */
/*   State: */
/*       a::arrI<cur'>@M *  */
/*  base'::arr_seg_max<v_int_97_2594,tmp_index',v1_2592,Anon_2593>@M *  */
/*  base'::arr_seg_max<tmp_index',m',v1,tmp_index'>@M& */
/* v_int_97_2594=i+1 & i'=i & base'=a-i & Anon_19=i & m=m' & Anon_18=cur' &  */
/* base=a-i & 0<=i & i<tmp_index' & tmp_index'<=(m'-2) & cur'<=tmp' &  */
/* v1_2592<=tmp' & v1<=tmp' & i<(a+tmp_index')&{FLOW,(4,5)=__norm#E}[] */
/*      es_gen_impl_vars(E): [] */
/*      es_pure: m'=m' & v1<=v_2696 & x=tmp_index'+base' &  */
/*               flted_63_2646=1+tmp_index' & a_2640=tmp_index'+base' &  */
/*               p=tmp_index' & m'=m' & tmp_index'=tmp_index' & m'=m' &  */
/*               v_int_95_2541=v_int_97_2040' & p=tmp_index' & tmp_index'<m' &  */
/*               v_int_97_2040'<=tmp_index' & n_2474=m' &  */
/*               flted_15_2475=v_int_95_2028' & v_int_95_2028'<m' & a=i'+base' */
/*      es_subst (from,to): []:[] */
/*      es_cond_path: [2; 2; 0] */
/*      es_var_measures 1: Some(MayLoop[]{}) */
     
/*     CtxOR */
/*       a::arrI<cur'>@M *  */
/*  base'::arr_seg_max<v_int_97_2618,tmp_index',v1_2616,Anon_2617>@M *  */
/*  base'::arr_seg_max<tmp_index',m',v1,tmp_index'>@M& */
/* i'=v_int_97_2618-1 & base'=(a-v_int_97_2618)+1 & m=m' &  */
/* base=(a-v_int_97_2618)+1 & i=v_int_97_2618-1 & 1<=v_int_97_2618 &  */
/* v_int_97_2618<=tmp_index' & tmp_index'<=(m'-2) & cur'<=tmp' &  */
/* cur'<=Anon_18 & v1_2616<=tmp' & v1<=tmp' & v_int_97_2618<=(a+tmp_index') &  */
/* ((v_int_97_2618<=Anon_19 | (Anon_19+2)<=v_int_97_2618))& */
/* {FLOW,(4,5)=__norm#E}[] */
/*      es_gen_impl_vars(E): [] */
/*      es_pure: m'=m' & v1<=v_2696 & x=tmp_index'+base' &  */
/*               flted_63_2656=1+tmp_index' & a_2640=tmp_index'+base' &  */
/*               p=tmp_index' & m'=m' & tmp_index'=tmp_index' & m'=m' &  */
/*               v_int_95_2543=v_int_97_2040' & p=tmp_index' & tmp_index'<m' &  */
/*               v_int_97_2040'<=tmp_index' & n_2483=m' &  */
/*               flted_16_2485=v_int_95_2028' & v_int_95_2028'<m' & a=i'+base' */
/*      es_subst (from,to): []:[] */
/*      es_cond_path: [2; 2; 0] */
/*      es_var_measures 1: Some(MayLoop[]{}) */
     
    
/*   Exc:None */
/*   ] */




