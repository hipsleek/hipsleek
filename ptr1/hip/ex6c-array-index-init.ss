data arrI {
  int val;
}

arr_seg<i,n> == i=n & i>=0
  or x::arrI<_>*self::arr_seg<i+1,n> & x=self+i & i>=0
  inv n>=i & i>=0;

arr_seg_zero<i,n> == i=n & i>=0
  or x::arrI<0>*self::arr_seg_zero<i+1,n> & x=self+i & i>=0
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
void init2(arrI base,int i)
  requires base::arr_seg<i,m> & m=10 & 0<=i & i<=m
  ensures  base::arr_seg_zero<i,m>;
{
  if (i<10) {
    upd_arr(base,i,0);
    i=i+1;
    //a = arr_inc(a);
    init2(base,i);
  }
}


/*
ex6b.ss (due to incomplete same_base computation)


# can we automatically determine ghost parameter 
  base=a-i, based on the values of the parameters a,i?

# can base be monomorphic recursive?

void init2(arrI a,int i)
  requires base::arr_seg<i,m> & a=base+i & m=10 & 0<=i & i<=m
  ensures  base::arr_seg_zero<i,m>;
{
Exception Failure("**context.ml#750:view matching..") Occurred!




*/
