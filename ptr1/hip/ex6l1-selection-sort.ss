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

arr_seg_max<i,n,maxv> == x::arrI<maxv> & x=self+i & i=n-1 & i>=0 //& cur<=max_value
  or x::arrI<cur> * self::arr_seg_max<i+1,n,maxv2> & x=self+i & i>=0 & i<n-1 & maxv=max(cur,maxv2)
  inv n>i & i>=0;

arr_seg_max_1<i,n,maxv> == i=n & i>=0 //& cur<=max_value
  or x::arrI<maxv> & x=self+i & i=n-1 & i>=0
  or x::arrI<cur> * self::arr_seg_max_1<i+1,n,maxv2> & x=self+i & i>=0 & i<n & maxv=max(cur,maxv2) & maxv>=cur & maxv>=maxv2
  inv n>i & i>=0;

arr_seg_max_2<i,n,maxv> == i=n & i>=0 //& cur<=max_value
  or x::arrI<cur> * self::arr_seg_max_2<i+1,n,maxv2> & x=self+i & i>=0 & i<n & maxv=max(cur,maxv2)
  inv n>i & i>=0;



arr_seg_sorted<i,n,ma,mi> == i=n & i>=0
  or x::arrI<m1> * self::arr_seg_sorted<i+1,n,m2,mi> &  m1>m2
  or self::arr_seg_sorted<i,n-1,ma,m1> * x::arrI<m2> & m1>m2
  inv n>i & i>=0;


void merge_max(arrI base,int i, int k, int n, int m)
  requires base::arr_seg_max_2<i,k,m1> * base::arr_seg_max_2<k,n,m2> & m1<=m & m2<=m
  ensures base::arr_seg_max_2<i,n,m>;

void merge_max_simp(arrI base,int i, int k, int n, int m)
  requires base::arr_seg_max_2<i,k,_> * base::arr_seg_max_2<k,n,_>
  ensures base::arr_seg_max_2<i,n,m>;

void reverse_unfold(arrI base, int i,int n,int m)
  requires x::arrI<m1>*base::arr_seg_max_2<i+1,n,m2> & x=base+i & m>=m1 & m>=m2
  ensures base::arr_seg_max_2<i,n,m>;

/* void unfold(arrI base, int i, int m) */
/*   requires base::arr_seg_max_2<i,m,m1> & i<m */
/*   ensures x::arrI<m2>*base::arr_seg_max_2<i+1, */

void reverse_unfold_simp(arrI base, int i,int n,int m)
  requires x::arrI<_>*base::arr_seg_max_2<i+1,n,_> & x=base+i
  ensures base::arr_seg_max_2<i,n,m>;

void merge(arrI base, int i, int k, int n,int m)
  requires base::arr_seg_max_2<i,k,_> * x::arrI<_> * base::arr_seg_max_2<k+1,n,_>
  ensures base::arr_seg_max_2<i,n,m>;

void upd_arr(arrI base, int i, int v)
  requires a::arrI<_> & a=base+i & i>=0
  ensures a::arrI<v> & a=base+i;

arrI arr_inc(arrI a)
  requires true //a::arrI<_>@L
  ensures res=a+1;

int get_arr(arrI base, int i)
  requires a::arrI<v>@L & a=base+i
  ensures res=v;

int get_max(arrI base,int i,int m)
  requires base::arr_seg_max_2<i,m,_> & i<m // generalization
  ensures  base::arr_seg_max_2<i,res,v1> * x::arrI<v> * base::arr_seg_max_2<res+1,m,v2> & v1<=v & v2<=v & x=base+res & res>=i & res<=m;
{
  if(i==m-1)
    {
      return i;
    }
  else{
    int cur = get_arr(base,i);
    int tmp_index = get_max(base,i+1,m);
    int tmp = get_arr(base,tmp_index);
    if(tmp<cur)
      {
        merge_max(base,i+1,tmp_index,m,tmp);
        return i;
      }
    else
      {
        reverse_unfold(base,i,tmp_index,tmp);
        return tmp_index;
      }
  }
}

void selection_sort(arrI base, int i, int m)
  requires base::arr_seg_max_2<i,m,_>
  ensures base::arr_seg_sorted<i,m,_,_>;
{
  if(i<m-1){
    int val = get_arr(base,i);
    int tmp_index = get_max(base,i+1,m);
    dprint;
    int tmp = get_arr(base,tmp_index);
    dprint;
    if(tmp<val){
      dprint;
      upd_arr(base,tmp_index,val);
      dprint;
      upd_arr(base,i,tmp);
      dprint;
      reverse_unfold_simp(base,tmp_index+1,m,val);
    }
    else{
      reverse_unfold_simp(base,tmp_index+1,m,tmp);
    }
    merge_max_simp(base,i+1,tmp_index,m,tmp);

    return selection_sort(base,i+1,m);
  }
  else{
    // assume false;
    return;
  }
}



/* /\* checkentail base'::arr_seg_max_1<flted_20_3168,n_3167,maxv2_3171>@M * base'::arr_seg_max_1<flted_20_3173,n_3172,maxv2_3176>@M * x_3169::arrI<cur_3170>@M& *\/ */
/* /\* base'<=x_3428 & cur_3175=m2 & x_3428=x_3174 & tmp'=v & v=v_2986 & a=x_2987 & *\/ */
/* /\* x_2987=tmp_index'+base' & v2_2985<=v_2986 & v1_2984<=v_2986 & *\/ */
/* /\* flted_60_2983=1+tmp_index' & 0<=i_2954 & i_2954<m_2955 & Anon_15=Anon_16 & *\/ */
/* /\* base'=base & i'=i & m'=m & i_2954=i & m_2955=m & i'<m' & v_bool_87_2088' & *\/ */
/* /\* n_3172=m' & maxv2_3176<=v2_2985 & cur_3175<=v2_2985 & v2_2985=max(cur_3175, *\/ */
/* /\* maxv2_3176) & flted_60_2983<m' & 0<=flted_60_2983 & *\/ */
/* /\* x_3174=flted_60_2983+base' & flted_20_3173=1+flted_60_2983 & *\/ */
/* /\* n_3167=tmp_index' & maxv2_3171<=v1_2984 & cur_3170<=v1_2984 & *\/ */
/* /\* v1_2984=max(cur_3170,maxv2_3171) & i'<tmp_index' & 0<=i' & x_3169=i'+base' & *\/ */
/* /\* flted_20_3168=1+i' & a_2994=x_3169 & v_2995=cur_3170 & val'=v_2995 & *\/ */
/* /\* x=x_2987 & m1=v_2986 & MayLoop[]&{FLOW,(4,5)=__norm#E}[] *\/ */
/* /\*  |-  (exists n_3412,flted_39_3413: emp& *\/ */
/* /\* flted_39_3413=1+tmp_index' & x=tmp_index'+base' & m1<=tmp' & m2<=tmp' & *\/ */
/* /\* n_3412=m' & cur_3175=m2 & 0<=flted_39_3413 & flted_39_3413+1=n_3412 & *\/ */
/* /\* x_3428=flted_39_3413+base'&{FLOW,(4,5)=__norm#E}[]). *\/ */

/* /\*  checkentail base'::arr_seg_max_1<flted_20_3168,n_3167,maxv2_3171>@M * base'::arr_seg_max_1<tmp_index',m',tmp'>@M * x_3169::arrI<cur_3170>@M& *\/ */
/* /\* flted_20_3173<=n_3172 & 1<=flted_20_3173 & base'=(x_3174-flted_20_3173)+1 &  *\/ */
/* /\* m2=max(cur_3449,maxv2_3450) & cur_3449<=m2 & maxv2_3450<=m2 &  *\/ */
/* /\* x_3174<(base'+n_3172) & base'<=x_3174 & flted_20_3173=(x_3174-base')+1 &  *\/ */
/* /\* maxv2_3450=maxv2_3176 & cur_3449=cur_3175 & tmp'=v & v=v_2986 & a=x_2987 &  *\/ */
/* /\* x_2987=tmp_index'+base' & v2_2985<=v_2986 & v1_2984<=v_2986 &  *\/ */
/* /\* flted_60_2983=1+tmp_index' & 0<=i_2954 & i_2954<m_2955 & Anon_15=Anon_16 &  *\/ */
/* /\* base'=base & i'=i & m'=m & i_2954=i & m_2955=m & i'<m' & v_bool_87_2088' &  *\/ */
/* /\* n_3172=m' & maxv2_3176<=v2_2985 & cur_3175<=v2_2985 & v2_2985=max(cur_3175, *\/ */
/* /\* maxv2_3176) & flted_60_2983<m' & 0<=flted_60_2983 &  *\/ */
/* /\* x_3174=flted_60_2983+base' & flted_20_3173=1+flted_60_2983 &  *\/ */
/* /\* n_3167=tmp_index' & maxv2_3171<=v1_2984 & cur_3170<=v1_2984 &  *\/ */
/* /\* v1_2984=max(cur_3170,maxv2_3171) & i'<tmp_index' & 0<=i' & x_3169=i'+base' &  *\/ */
/* /\* flted_20_3168=1+i' & a_2994=x_3169 & v_2995=cur_3170 & val'=v_2995 &  *\/ */
/* /\* x=x_2987 & m1=v_2986 & flted_20_3173<n_3172 & 0<=flted_20_3173 &  *\/ */
/* /\* x_3174!=null & x_2987!=null & v_int_96_2087'=1+i' & MayLoop[]& *\/ */
/* /\* {FLOW,(4,5)=__norm#E}[] *\/ */
/* /\*  |-  (exists i_6253,k_6254,k_6255, *\/ */
/* /\* n_6256: base'::arr_seg_max_1<k_6255,n_6256,Anon_13>@M& *\/ */
/* /\* i_6253=v_int_96_2087' & k_6254=tmp_index' & k_6255=tmp_index' & n_6256=m' &  *\/ */
/* /\* 0<=i_6253 & i_6253=k_6254&{FLOW,(4,5)=__norm#E}[]).  *\/ */

/* /\* checkentail base'::arr_seg_max_1<i',tmp_index',v1_2975>@M * base'::arr_seg_max_1<tmp_index',m',tmp'>@M&v_bool_87_2079' & i'<m' & m_2946=m & i_2945=i & m'=m & i'=i & base'=base &  *\/ */
/* /\* Anon_15=Anon_16 & i_2945<m_2946 & 0<=i_2945 & flted_60_2974=1+tmp_index' &  *\/ */
/* /\* v1_2975<=v_2977 & v2_2976<=v_2977 & x_2978=tmp_index'+base' & a=x_2978 &  *\/ */
/* /\* v=v_2977 & tmp'=v & x=x_2978 & m1=v_2977 & m2=v2_2976 & flted_60_2974<m' &  *\/ */
/* /\* 0<=flted_60_2974 & x_2978!=null & v_int_96_2078'=1+i' & MayLoop[]& *\/ */
/* /\* {FLOW,(4,5)=__norm#E}[] *\/ */
/* /\*  |-  (exists i_187,k_188,k_189, *\/ */
/* /\* n_190: base'::arr_seg_max_1<i_187,k_188,Anon_12>@M *  *\/ */
/* /\*        base'::arr_seg_max_1<k_189,n_190,Anon_13>@M& *\/ */
/* /\* i_187=v_int_96_2078' & k_188=tmp_index' & k_189=tmp_index' & n_190=m'& *\/ */
/* /\* {FLOW,(4,5)=__norm#E}[]).  *\/ */

/* /\*  checkentail base'::arr_seg_max_1<flted_20_3167,n_3166,maxv2_3170>@M * x_3163::arrI<cur_3164>@M& *\/ */
/* /\* (((cur_3812=Anon_13 & maxv2_3813<=Anon_13) |  (maxv2_3813=Anon_13 & cur_3812<Anon_13))) &base'<x_3835 & x_2981=x_3835-1 & cur_3169=maxv2_3813 & cur_3812=v_2980 &  *\/ */
/* /\* tmp'=v & v=v_2980 & a=x_2981 & x_2981=tmp_index'+base' & v2_2979<=v_2980 &  *\/ */
/* /\* v1_2978<=v_2980 & flted_60_2977=1+tmp_index' & 0<=i_2948 & i_2948<m_2949 &  *\/ */
/* /\* Anon_15=Anon_16 & base'=base & i'=i & m'=m & i_2948=i & m_2949=m & i'<m' &  *\/ */
/* /\* v_bool_87_2082' & n_3166=m' & maxv2_3170<=v2_2979 & cur_3169<=v2_2979 &  *\/ */
/* /\* v2_2979=max(cur_3169,maxv2_3170) & flted_60_2977<m' & 0<=flted_60_2977 &  *\/ */
/* /\* x_3168=flted_60_2977+base' & flted_20_3167=1+flted_60_2977 &  *\/ */
/* /\* n_3161=tmp_index' & maxv2_3165<=v1_2978 & cur_3164<=v1_2978 &  *\/ */
/* /\* v1_2978=max(cur_3164,maxv2_3165) & i'<tmp_index' & 0<=i' & x_3163=i'+base' &  *\/ */
/* /\* flted_20_3162=1+i' & a_2988=x_3163 & v_2989=cur_3164 & val'=v_2989 &  *\/ */
/* /\* v_int_96_2081'=1+i' & Anon_12=maxv2_3165 & x_3835=x_3168 & base'<=x_3835 &  *\/ */
/* /\* MayLoop[]&{FLOW,(4,5)=__norm#E}[] *\/ */
/* /\*  |-  (exists k_3792,n_3793: emp& *\/ */
/* /\* flted_20_3162=v_int_96_2081' & n_3161=tmp_index' & k_3792=tmp_index' &  *\/ */
/* /\* n_3793=m' & x_2981=k_3792+base' & 0<=k_3792 & k_3792<n_3793 &  *\/ */
/* /\* Anon_13=max(cur_3812,maxv2_3813) & cur_3812<=Anon_13 & maxv2_3813<=Anon_13 &  *\/ */
/* /\* x_3835=1+k_3792+base' & 0<=(1+k_3792) & 1+k_3792+1=n_3793& *\/ */
/* /\* {FLOW,(4,5)=__norm#E}[]).  *\/ */

/*  checkentail base'::arr_seg_max_2<flted_24_2960,n_2959,maxv2_2963>@M *  */
/*  base'::arr_seg_max_2<flted_24_2965,n_2964,maxv2_2968>@M *  */
/*  x_2966::arrI<cur_2967>@M * a_2997::arrI<tmp'>@M& */
/* tmp'=v & v=v_2859 & a=x_2860 & tmp_index'<=m' & i'<=tmp_index' &  */
/* x_2860=tmp_index'+base' & v2_2858<=v_2859 & v1_2857<=v_2859 &  */
/* flted_65_2856=1+tmp_index' & 0<=i_2827 & i_2827<m_2828 & Anon_15=Anon_16 &  */
/* base'=base & i'=i & m'=m & i_2827=i & m_2828=m & i'<m' & v_bool_92_2137' &  */
/* n_2964=m' & v2_2858=max(cur_2967,maxv2_2968) & flted_65_2856<m' &  */
/* 0<=flted_65_2856 & x_2966=flted_65_2856+base' &  */
/* flted_24_2965=1+flted_65_2856 & n_2959=tmp_index' & v1_2857=max(cur_2962, */
/* maxv2_2963) & i'<tmp_index' & 0<=i' & x_2961=i'+base' & flted_24_2960= */
/* 1+i' & a_2867=x_2961 & v_2868=cur_2962 & val'=v_2868 & a_2978=x_2860 &  */
/* Anon_14=v_2859 & x_2860!=null & a_2978=tmp_index'+base' & a_2997=x_2961 &  */
/* Anon_2998=cur_2962 & x_2961!=null & a_2997=i'+base' & x=a_2978 & m1=val' &  */
/* MayLoop[]&{FLOW,(4,5)=__norm#E}[] */
/*  |-  (exists n_3082,flted_44_3083: emp& */
/* flted_44_3083=1+tmp_index' & x=tmp_index'+base' & m1<=tmp' & m2<=tmp' & */
/* n_3082=m' & 0<=flted_44_3083 & flted_44_3083=n_3082&{FLOW,(4,5)=__norm#E}[]).  */
