data arrI {
  int val;
}

arr_seg<i,n> == i=n & i>=0
  or x::arrI<_>*self::arr_seg<i+1,n> & x=self+i & i>=0
  inv n>=i & i>=0;


arr_seg_max<i,n,maxv,pos> == i=n & i>=0 //& cur<=max_value
  or x::arrI<cur> * self::arr_seg_max<i+1,n,maxv2,pos> & x=self+i & i>=0 & i<n-1 & ((!(i=pos))|(cur=maxv)) & maxv=max(cur,maxv2)
  inv n>i & i>=0;

void split_arr(arrI base,int i,int m,int k)
  requires base::arr_seg<i,m> & i<=k & k<m
  ensures base::arr_seg<i,k> * base::arr_seg<k,m>;

void merge_arr(arrI base,int i,int m,int k)
  requires base::arr_seg<i,k> * base::arr_seg<k,m>
  ensures base::arr_seg<i,m>;


void reverse_unfold(arrI base, int i, int m)
  requires x::arrI<v> * base::arr_seg<i+1,m> & x=base+i
  ensures base::arr_seg<i,m>;

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
        // (i) [i+1...tmp_index) (tmp_index) [tmp_index+1...m) |- [i...m]
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
