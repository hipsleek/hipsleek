data arrI {
  int val;
}

arr_seg<i,n> == i=n & i>=0
  or x::arrI<_>*self::arr_seg<i+1,n> & x=self+i & i>=0
  inv n>=i & i>=0;

arr_seg_sorted<i,n,mi> == x::arrI<v> & x=self+i & i=n-1 & i>=0 & v<=mi
  or x::arrI<v>*self::arr_seg_sorted<i+1,n,m2> & x=self+i & i>=0 & i<n-1 & v<=mi & mi>=m2 & v>=m2
  inv n>i & i>=0;

/* arr_seg_max<i,n,maxv> == x::arrI<maxv> & x=self+i & i=n-1 & i>=0 //& cur<=max_value */
/*   or x::arrI<cur> * self::arr_seg_max<i+1,n,maxv2> & x=self+i & i>=0 & i<n-1 & maxv=max(cur,maxv2) */
/*   inv n>i & i>=0; */

/* arr_seg_max_1<i,n,maxv> == i=n & i>=0 //& cur<=max_value */
/*   or x::arrI<maxv> & x=self+i & i=n-1 & i>=0 */
/*   or x::arrI<cur> * self::arr_seg_max_1<i+1,n,maxv2> & x=self+i & i>=0 & i<n & maxv=max(cur,maxv2) & maxv>=cur & maxv>=maxv2 */
/*   inv n>i & i>=0; */

/* arr_seg_max_2<i,n,maxv> == i=n & i>=0 //& cur<=max_value */
/*   or x::arrI<cur> * self::arr_seg_max_2<i+1,n,maxv2> & x=self+i & i>=0 & i<n & maxv=max(cur,maxv2) & maxv>=cur & maxv>=maxv2 */
/*   inv n>=i & i>=0; */

arr_seg_max_3<i,n,maxv> == x::arrI<maxv> & x=self+i & i=n-1 & i>=0
  or x::arrI<cur> * self::arr_seg_max_3<i+1,n,maxv2> & x=self+i & i>=0 & i<n-1 & maxv=max(cur,maxv2) & maxv>=cur & maxv>=maxv2
  inv n>i & i>=0;



/* arr_seg_sorted<i,n,ma,mi> == i=n & i>=0 */
/*   or x::arrI<m1> * self::arr_seg_sorted<i+1,n,m2,mi> &  m1>m2 */
/*   or self::arr_seg_sorted<i,n-1,ma,m1> * x::arrI<m2> & m1>m2 */
/*   inv n>i & i>=0; */


void merge_max(arrI base,int i, int k, int n, int m)
  requires base::arr_seg_max_2<i,k,m1> * base::arr_seg_max_2<k,n,m2> & m1<=m & m2<=m
  ensures base::arr_seg_max_2<i,n,m>;

/* void merge_max_simp(arrI base,int i, int k, int n, int m) */
/*   requires base::arr_seg_max_1<i,k,_> * base::arr_seg_max_1<k,n,_> */
/*   ensures base::arr_seg_max_1<i,n,m>; */

void reverse_unfold(arrI base, int i,int n,int m)
  requires x::arrI<m1>*base::arr_seg_max_2<i+1,n,m2> & x=base+i & m1<=m & m2<=m
  ensures base::arr_seg_max_2<i,n,m>;

void reverse_unfold_simp(arrI base, int i,int n,int m)
  requires x::arrI<m1>*base::arr_seg_max_2<i+1,n,m2> & x=base+i
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
  requires base::arr_seg_max_3<i,m,_> & i<m // generalization
  ensures  (base::arr_seg_max_3<i,(base::arr_seg_max_3<i,res,v1> * x::arrI<v> * base::arr_seg_max_3<res+1,m,v2> & v>=v1 & v>=v2 & x=base+res);
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

/* void reverse_unfold_sort(arrI base, int i, int m) */
/*   requires x::arrI<v>*base::arr_seg_sorted<i+1,m,mv> & x=base+i & mv<=v */
/*   ensures base::arr_seg_sorted<i,m,v>; */


/* void selection_sort(arrI base, int i, int m) */
/*   requires base::arr_seg_max_2<i,m,maxv> & i<m */
/*   ensures base::arr_seg_sorted<i,m,maxv>; */
/* { */
/*   if(i==m-1){ */
/*     assume false; */
/*     get_arr(base,i); // Just to enforce the unfolding */
/*     //dprint; */
/*     return; //get_arr(base,i); */
/*   } */
/*   else{ */

/*     // assume false; */
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
/*     // reverse_unfold(base,tmp_index,m,tmp); */
/*     //    dprint; */
/*     merge_max(base,i+1,tmp_index,m,tmp); */
/*     //    dprint; */
/*     //get_arr(base,i); */
/*     selection_sort(base,i+1,m); */
/*     dprint; */
/*     reverse_unfold_sort(base,i,m); */
/*     return; */
/*   } */
/* } */



