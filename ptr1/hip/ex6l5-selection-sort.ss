data arrI {
  int val;
}

arr_seg<i,n,S> == i=n & i>=0 & S={}
  or x::arrI<v>*self::arr_seg<i+1,n,S2> & x=self+i & i>=0 & S=union({v},S2)
  inv n>=i & i>=0;

/* arr_seg_sorted<i,n,mi> == x::arrI<mi> & x=self+i & i=n-1 & i>=0 */
/*   or x::arrI<mi>*self::arr_seg_sorted<i+1,n,m2> & x=self+i & i>=0 & i<n-1 & mi>=m2 */
/*   inv n>i & i>=0; */


/* arr_seg_max_2<i,n,maxv> == i=n & i>=0 //& cur<=max_value */
/*   or x::arrI<cur> * self::arr_seg_max_2<i+1,n,maxv2> & x=self+i & i>=0 & i<n & maxv=max(cur,maxv2) */
/*   inv n>=i & i>=0; */


/* void merge_max(arrI base,int i, int k, int n, int m) */
/*   requires base::arr_seg_max_2<i,k,m1> * base::arr_seg_max_2<k,n,m2> & m1<=m & m2<=m */
/*   ensures base::arr_seg_max_2<i,n,m>; */


/* void reverse_unfold(arrI base, int i,int n,int m) */
/*   requires x::arrI<m1>*base::arr_seg_max_2<i+1,n,m2> & x=base+i & m1<=m & m2<=m */
/*   ensures base::arr_seg_max_2<i,n,m>; */

/* void reverse_unfold_simp(arrI base, int i,int n,int m) */
/*   requires x::arrI<m1>*base::arr_seg_max_2<i+1,n,m2> & x=base+i */
/*   ensures base::arr_seg_max_2<i,n,m>; */

void unfold_arr(arrI base, int i, int m)
  requires base::arr_seg<i,m,S> & i<m
  ensures x::arrI<v> * base::arr_seg<i+1,m,S1> & S=union(S1,{v});

void base_case_fold_arr(arrI base, int i, int m)
  requires i=m
  ensures base::arr_seg<i,m,{}>;

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
  requires base::arr_seg<i,m,S> & i<m // generalization
  ensures  base::arr_seg<i,res,S1> * x::arrI<v> * base::arr_seg<res+1,m,S2> & x=base+res & S=union(S1,S2,{v});
{
  if(i==m-1)
    {
      unfold_arr(base,i,m);
      base_case_fold_arr(base,i,m-1);
      dprint;
      return i;
    }
  else{
    assume false;
    int cur = get_arr(base,i);
    int tmp_index = get_max(base,i+1,m);
    int tmp = get_arr(base,tmp_index);
    if(tmp<cur)
      {
        return i;
      }
    else
      {
        return tmp_index;
      }
  }
}

/* int selection_sort(arrI base, int i, int m, int ma) */
/*   requires base::arr_seg_max_2<i,m,ma> & i<m */
/*   ensures base::arr_seg_sorted<i,m,res>; */
/* { */
/*   if(i==m-1){ */
/*     return get_arr(base,i); */
/*   } */
/*   else{ */
/*     //assume false; */
/*     // dprint; */
/*     int val = get_arr(base,i); */
/*     int tmp_index = get_max(base,i+1,m); */
/*     int tmp = get_arr(base,tmp_index); */
/*     //reverse_unfold(base,tmp_index,m,tmp); */
/*     if(tmp>val){ */
/*       upd_arr(base,tmp_index,val); */
/*       upd_arr(base,i,tmp); */
/*     } */
/*     //    dprint; */
/*     reverse_unfold(base,tmp_index,m,tmp); */
/*     //    dprint; */
/*     merge_max(base,i+1,tmp_index,m,tmp); */
/*     //    dprint; */
/*     int ma = get_arr(base,i); */
/*     selection_sort(base,i+1,m); */
/*     dprint; */
/*     return ma; */
/*   } */
/* } */
