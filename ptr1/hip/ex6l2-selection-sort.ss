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

arr_seg_max<i,n,maxv,pos> == i=n & i>=0 //& cur<=max_value
  or x::arrI<cur> * self::arr_seg_max<i+1,n,maxv2,pos> & x=self+i & i>=0 & i<n-1 & ((!(i=pos))|(cur=maxv)) & maxv=max(cur,maxv2)
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
  requires base::arr_seg<i,m> & i<=k & k<m
  ensures base::arr_seg<i,k> * base::arr_seg<k,m>;

void merge_arr(arrI base,int i,int m,int k)
  requires base::arr_seg<i,k> * base::arr_seg<k,m>
  ensures base::arr_seg<i,m>;


void reverse_unfold(arrI base, int i, int m)
  requires x::arrI<v> * base::arr_seg<i+1,m> & x=base+i
  ensures base::arr_seg<i,m>;
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
  ensures  base::arr_seg<i,m>&res>=i&res<m;
{
  if(i==m-1)
    {
      return i;
    }
  else{
    int cur = get_arr(base,i);
    int tmp_index = get_max(base,i+1,m);
    split_arr(base,i+1,m,tmp_index);
    int tmp = get_arr(base,tmp_index);
    //    dprint;

    if(tmp<cur)
      {
        reverse_unfold(base,tmp_index,m);
        merge_arr(base,i+1,m,tmp_index);
        return i;
      }
    else
      {
        reverse_unfold(base,tmp_index,m);
        merge_arr(base,i+1,m,tmp_index);
        return tmp_index;
      }
  }
}
