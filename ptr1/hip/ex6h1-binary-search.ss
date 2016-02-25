data arrI{
  int val;
}

arr_seg<i,n> == i=n & i>=0
  or x::arrI<_>*self::arr_seg<i+1,n> & x=self+i & i>=0
  inv n>=i & i>=0;

arr_seg_sorted_aux<i,n,mi> == x::arrI<mi> & x=self+i & i=n-1 & i>=0
  or x::arrI<mi>*self::arr_seg_sorted_aux<i+1,n,m2> & x=self+i
       & i>=0 & i<n-1 & mi<=m2
  inv n>i & i>=0;

arr_seg_sorted<i,n> == i=n-1
  or x::arrI<m1> * self::arr_seg_sorted_aux<i+1,n,m2> & x = self+i
  & i>=0 & i<n-1 & m1<=m2
  inv n>i & i>=0;

arr_pos_val<i,v,n> == i=n & i>=0 or
  self::arr_seg<i,n> * x::arrI<v> & x = self + i
  inv n>=i & i>=0;

void upd_arr(arrI base, int i, int v)
  requires a::arrI<_> & a=base+i & i>=0
  ensures a::arrI<v>;

arrI arr_inc(arrI a)
  requires true //a::arrI<_>@L
  ensures res=a+1;

int get_arr(arrI base, int i)
  requires a::arrI<v>@L & a=base+i //
  ensures res=v;


int binary_search(arrI arr, int s, int e,int target)
  requires arr::arr_seg<1,10>
  ensures arr::arr_pos_val<res,target,e-s>;
{
  int mid = get_arr(arr,2);
  return 0;

}
