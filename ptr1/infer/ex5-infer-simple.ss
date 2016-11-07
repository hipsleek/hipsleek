relation U(int u1,int u2).
data arrI
{
 int value;
}

void upd_arr(arrI base, int i, int v)
  requires base::arr_seg<u,w>  & u<=i & w>=i+1 & i>=0
  ensures base::arr_seg<u,w>;

arr_seg<i,n> == i=n & i>=0
    or x::arrI<_>*self::arr_seg<i+1,n> & x=self+i & i>=0
inv n>=i & i>=0;


void init2(arrI a)
   infer[U]
   requires a::arr_seg<u1,u2> & U(u1,u2)
   ensures  a::arr_seg<u1,u2>;
  {
    upd_arr(a,5,0);
  }


/*
[RELASS [U]: ( U(u1,u2)) -->  ((u2<=u1 & 6<=u1) | (u2<=u1 & 0<=u1 & u1<=4) | 
                               (0<=u1 & u1<=(u2-2) & u1<=4) | u1=5 | (6<=u1 & u1<=(u2-2)) | u1<=(0-1)),
RELASS [U]: ( U(u1,u2)) -->  (u1!=u2 | 0>u2),
        RELASS [U]: ( U(u1,u2)) -->  ((u2=6 & 4<=u1) | (7<=u2 & u2<=(u1+1)) | 
                                      (u2<=5 & u2<=(u1+2) & (5*u2)<=(9+(4*u1))) | (u1=4 & 7<=u2) | 
                                      (u1<=(u2-3) & u1<=(0-1))),
        RELASS [U]: ( U(u1,u2)) -->  ((8<=u2 & u2<=(u1+1)) | (u2<=(u1+2) & u2<=1) | 
                                      (2<=u2 & u2<=7 & (4*u2)<=(3+(5*u1))) | (u1=5 & 8<=u2) | 
                                      (u1<=(0-1) & u1<=(u2-3))),
        RELASS [U]: ( U(u1,u2)) -->  (u1=5 | (u2<=u1 & 6<=u1) | u1<=(0-1) | (u1<=4 & 0<=u1 & u2<=u1))]


[RELASS [U]: ( U(u1,u2)) -->  (u2!=u1 | 0>u1),
RELASS [U]: ( U(u1,u2)) -->  ((u2=u1 & 0<=u1) | (u2=6 & u1=5))]

[RELASS [U]: ( U(u1,u2)) -->  ((u2=u1 & u1!=u2) | (u1<=5 & 6<=u2 & 0>u2) | (u1<=5 & 6<=u2 & u1!=u2) | 
  (u2=u1 & 0>u2))]

*/
