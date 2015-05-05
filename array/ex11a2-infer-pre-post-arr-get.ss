//hip_include '../prelude_aux.ss'
//#option --ato
relation P(int a).
relation Q(int a,int r).

int foo(int[] a)
 //infer [@arrvar] requires true ensures res=a[5];
  infer [@arrvar,P,Q] requires P(a) ensures Q(res,a[5]);
//  infer [@arrvar,P] requires true ensures P(res,a[4]);
{
  if (a[5]>10) {
    return a[5];
  } else {
    assume false;
    return -1;
  }
}

/*
# ex11a2.ss

!!! **pi.ml#610: Q(res,a[5]) = ( a[5]=res & 11<=res)
!!! **pi.ml#614:bottom_up_fp0:[( Q(a[5],res), a[5]=res & 11<=res)]
WARNING: _0:0_0:0:Z3 error message: (error "line 1256 column 25: invalid declaration, function 'P' (whith the given signature) already declared")

 */
