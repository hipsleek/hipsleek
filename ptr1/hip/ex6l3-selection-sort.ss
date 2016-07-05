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
  or x::arrI<cur> * self::arr_seg_max<i+1,n,maxv2,pos> & x=self+i & i>=0 & i<n-1 & pos>=i & pos<=n-1 & ((!(i=pos))|(maxv=cur)) & maxv=max(cur,maxv2)
  inv n>i & i>=0 & pos>=i & pos<=n-1;

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
  ensures  base::arr_seg_max<i,m,_,res>;
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
        return i;
      }
    else
      {
        return tmp_index;
      }
  }
}

