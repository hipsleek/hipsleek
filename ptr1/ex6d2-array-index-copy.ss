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

arr_seg_map<i,n,M> == i=n & i>=0
  or x::arrI<v>*self::arr_seg_map<i+1,n,M> & x=self+i & i>=0 & M[i]=v
  inv n>=i & i>=0;

arr_seg_map2<i,n,M> == i=n & i>=0
  or x::arrI<v>*self::arr_seg_map2<i+1,n,M> & x=self+i & i>=0 & M[i]+2=v
  inv n>=i & i>=0;

void upd_arr(arrI base, int i, int v)
  requires a::arrI<_> & a=base+i & i>=0
  ensures a::arrI<v>;

arrI arr_inc(arrI a)
  requires true //a::arrI<_>@L
  ensures res=a+1;

int get_arr(arrI base, int i)
  requires a::arrI<v>@L & a=base+i
  ensures res=v;

// can base be monomorphic recursive?
void copy(arrI base,arrI b2,int i,int m)
  requires base::arr_seg<i,m> * b2::arr_seg_map<i,m,M>@L//& 0<=i & i<=m
  ensures  base::arr_seg_map2<i,m,M>;
{
  if (i<m) {
    int v = get_arr(b2,i);
    upd_arr(base,i,v+2); // base[i]=0
    i=i+1;
    //a = arr_inc(a);
    copy(base,b2,i,m);
  }
}

/*
ex6c2.ss (due to incomplete same_base computation)

  requires base::arr_seg<i,m> * b2::arr_seg_map<i,m,M>@L//& 0<=i & i<=m
  ensures  base::arr_seg_map<i,m,M>;



*/
