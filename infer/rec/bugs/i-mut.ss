

relation R1(int h, int n).
relation R2(int h, int n).
relation R3(int h, int n).

int foo(int x)
  infer [R3]
  requires x>=0
  ensures  R3(res,x);
  // res=2*x+1;
{
  int r;
  if (x==0) r=1;
  else {
    int h=sum(x);
    r=1+foo(x-1);
  }
  return r;
}

int sum(int x)
  infer [R1,R2]
  requires x>=0
  ensures  R1(res,x);
  //ensures  res=x;
{
  int r;
  if (x==0) r=1;
  else {
    r=2+sum2(x-1);
  }
  return r;
}

int sum2(int x)
  infer [R1,R2]
  requires x>=0
  ensures  R2(res,x);
  //ensures  res=x;
{
  int r;
  if (x==0) r=1;
  else {
    r=2+sum(x-1);
  }
  return r;
}


/*

Why did we get a worse result with --fixcalc-disj 2.

!!! REL :  R2(res,x)
!!! POST:  res>=1 & x>=0
!!! PRE :  true
!!! REL :  R1(res,x)
!!! POST:  res>=1 & x>=0
!!! PRE :  true


With --fixcalc-disj 1, we got.
[( R1(res,x), x>=0 & res=(2*x)+1),
( R2(res,x), x>=0 & res=(2*x)+1)]


*/
