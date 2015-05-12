relation Q(int a, int b).
relation P(int a).

  int foo(int m)
  infer [P,Q]
  requires P(m)
     ensures Q(m,res);
{
  if (m==0) return 0;
    else return 2+foo(m-1);
}

/*
# ex6b.ss --esl

!!! fixcalc file name: logs/fixcalc.inf
!!! **pi.ml#619:bottom_up_fp0:[( Q(m,res), m>=0 & 2*m=res)]
!!! **pi.ml#636:fixpoint:[( Q(m,res), m>=0 & 2*m=res, P(m), 0<=m)]
!!! **pi.ml#650:>>REL POST :  Q(m,res)
!!! **pi.ml#651:>>POST:  m>=0 & 2*m=res
!!! **pi.ml#652:>>REL PRE :  P(m)
!!! **pi.ml#653:>>PRE :  0<=m


*/
