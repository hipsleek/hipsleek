
relation P(int n).
  relation Q(int n,int m,int r).


int id(ref int n)
  infer [P,Q]
  requires P(n) ensures Q(n,n',res);
{
  if (n==0) return 0;
  else return 1+id(n-1);
}



/*
# sim3-id.ss

For below:

!!! constraints:[( Q(v_int_11_1349,v_int_11_1352) & (v_int_11_1349+1)!=0 & v_int_11_1352+
1=res & n=1+v_int_11_1349, Q(n,res)),( n=0 & res=0, Q(n,res))]

Maybe better to print:
  Q(n,res) = base \/ rec_case

!!! bottom up
!!! fixcalc file name: fixcalc1.inf
!!! bottom_up_fp:[( Q(n,res), n=res & 0<=res)]
!!! fixpoint:[( Q(n,res), n=res & 0<=res, P(n), 0<=n)]

How did we get:
  P(n) = n>=0

*/
