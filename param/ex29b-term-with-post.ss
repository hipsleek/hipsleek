
relation R(int x,int y,int a,int b).

void loo (ref int x, ref int y,int a, int b)
  infer [@term]
  requires true
  ensures y<=0 & x<=0 & y=y' & x=x' | y'<=0 & x'<=0 & y+x>=2+y'+x';
{

  if (x>0 || y>0) {
    //dprint;
    x = x+a-b-1;
    y = y+b-a-1;
    loo(x,y,a,b);
  };
}

/*
# ex29b.ss

!!! **panalysis.ml#103:constraints of y':[ y=((x'+y')-x)+2]
!!! **panalysis.ml#103:constraints of a':[]
!!! **panalysis.ml#103:constraints of b':[]
ExceptionFailure("more constraints than assumed")Occurred!



 */
