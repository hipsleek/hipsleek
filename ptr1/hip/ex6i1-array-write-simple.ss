data arrI{
  int val;
}

arr_seg<i,n> == i=n & i>=0
  or x::arrI<_>*self::arr_seg<i+1,n> & x=self+i & i>=0
  inv n>=i & i>=0;

arr_pos_val<i,n,pos,v> ==
  i=n & i>0
  or self::arr_seg<i,pos> * x::arrI<v> * self::arr_seg<pos+1,n> & i<pos & pos<n & x=self+pos
  inv n>=i & i>=0;

/* lemma_unsafe self::arr_seg<i,n> & i<=m & m<=n */
/*    <-> self::arr_seg<i,m>*self::arr_seg<m,n>. */

void split_arr(arrI base, int k,int i,int n)
  requires base::arr_seg<i,n>
  ensures base::arr_seg<i,k> * base::arr_seg<k,n>;

void merge_arr(arrI base,int i,int k,int n)
  requires base::arr_seg<i,k> * base::arr_seg<k,n>
  ensures base::arr_seg<i,n>;

void upd_arr(arrI base, int i, int v)
  requires a::arrI<_> & a=base+i & i>=0
  ensures a::arrI<v>;

arrI arr_inc(arrI a)
  requires true //a::arrI<_>@L
  ensures res=a+1;

int get_arr(arrI base, int i)
  requires a::arrI<v>@L & a=base+i //
  ensures res=v;


void array_write(arrI arr)
  requires arr::arr_seg<1,10>
  ensures arr::arr_pos_val<1,10,3,7>;
//  ensures arr::arr_seg<1,3> * x::arrI<7> * arr::arr_seg<4,10> & x=arr+3 ;
//  ensures arr::arr_seg<1,10>;
{
  split_arr(arr,3,1,10);
  upd_arr(arr,3,7);
  //merge_arr(arr,1,3,10);
  return;
}
