

relation R1(int h, int n).
relation R2(int h, int n).


int foo(int x)
  requires x>=0
  ensures  res=2*x;
{
  int r;
  if (x==0) r=0;
  else {
    int h=sum(x);
    r=2+foo(x-1);
  }
  return r;
}

int sum(int x)
  infer [R1,R2]
  requires x>=0
  ensures  R1(res,x);
{
  int r;
  if (x==0) r=0;
  else {
    r=2+sum2(x-1);
  }
  return r;
}

int sum2(int x)
  infer [R1,R2]
  requires x>=0
  ensures  R2(res,x);
{
  int r;
  if (x==0) r=0;
  else {
    r=2+sum(x-1);
  }
  return r;
}


/*

PROBLEM : can we remove x>=0 which is already present
in precondition?

!!! REL :  R1(res,x)
!!! POST:  x>=0 & res=(2*x)+2
!!! PRE :  true

*/
