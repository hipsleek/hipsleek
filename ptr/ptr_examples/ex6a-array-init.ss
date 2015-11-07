
/*
array copy
void copy(ref int[] a,int[] b,int i){
   if(i<10){
      a[i]=b[i+k];
      init(a,i+1);
   }
}
*/
data arrI {
  int val;
}

arr_seg<i,n> == i=n & i>=0
  or x::arrI<_>*self::arr_seg<i+1,n> & x=self+i & i>=0
  inv n>=i & i>=0;

void upd_arr(arrI a, int v)
  requires a::arrI<_>
  ensures a::arrI<v>;

arrI arr_inc(arrI a)
  requires true //a::arrI<_>@L
  ensures res=a+1;

int get_arr(arrI a)
  requires a::arrI<v>@L
  ensures res=v;

void init(arrI a,int i,arrI base)
  requires base::arr_seg<i,m> & a=base+i & m=10 & 0<=i & i<=m
  ensures  base::arr_seg<i,m>;
{
  if (i<10) {
    upd_arr(a,0);
    i=i+1;
    a = arr_inc(a);
    init(a,i,base);
  }
}
