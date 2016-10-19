data arrI
{
 int value;
     }

relation U(int u1,int u2, int i).

void upd_arr(arrI base, int i, int v)
  requires a::arrI<_> & a = base+i & i>=0
  ensures a::arrI<_>;



arr_seg<i,n> == i=n & i>=0
    or x::arrI<_>*self::arr_seg<i+1,n> & x=self+i & i>=0
inv n>=i & i>=0;


void init2(arrI a, int i)
   infer[U]
   requires a::arr_seg<u1,u2> & U(u1,u2,i)
   ensures  a::arr_seg<u1,u2>;
  {
    upd_arr(a,i,0);
}


