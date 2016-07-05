data arrI {
  int val;
}

arr_seg<i,n> == i=n & i>=0
  or x::arrI<_>*self::arr_seg<i+1,n> & x=self+i & i>=0
  inv n>=i & i>=0;

arr_seg_zero<i,n> == i=n & i>=0
  or x::arrI<0>*self::arr_seg_zero<i+1,n> & x=self+i & i>=0
  inv n>=i & i>=0;

arr_seg_v<i,n,v> == i=n & i>=0
  or x::arrI<v>*self::arr_seg_v<i+1,n,v> & x=self+i & i>=0
  inv n>=i & i>=0;

void upd_arr(arrI base, int i, int v)
  requires a::arrI<_> & a=base+i & i>=0
  ensures a::arrI<v>;

arrI arr_inc(arrI a)
  requires true //a::arrI<_>@L
  ensures res=a+1;

int get_arr(arrI a)
  requires a::arrI<v>@L
  ensures res=v;

// can base be monomorphic recursive?
void init2(arrI base,int i,int m)
  requires base::arr_seg<i,m> //& 0<=i & i<=m
  ensures  base::arr_seg_v<i,m,0>;
{
  if (i<m) {
    upd_arr(base,i,0); // base[i]=0
    i=i+1;
    //a = arr_inc(a);
    init2(base,i,m);
  }
}

/*
ex6c1.ss (due to incomplete same_base computation)

  requires base::arr_seg<i,m> //& 0<=i & i<=m
  ensures  base::arr_seg_v<i,m,0>;


*/
