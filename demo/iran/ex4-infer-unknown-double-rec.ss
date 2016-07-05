relation Upost(int n, int r).

int double(int n)
  infer [Upost]
  requires true
  ensures  Upost(n,res);
{
  if (n==0) return 0;
  else return 2+double(n-1);
}

/*
# ex4.ss

RELDEFN Upost: 
  ( n=0 & res=0) -->  Upost(n,res),
  (Upost(v_int_9_1352,v_int_9_1354) & res=2+v_int_9_1354 
   & v_int_9_1352+1=n & n!=0) -->  Upost(n,res)]

!!!  Upost(n,res) = 
     ( Upost(v_int_9_1352,v_int_9_1354) & res=2+v_int_9_1354 
       & v_int_9_1352+1=n & n!=0) \/ ( n=0 & res=0)
!!! bottom_up_fp:[( Upost(n,res), n>=0 & 2*n=res)]

*/

