
int abs(int n)
 case {
   n<0 -> ensures res=-n;
   n>=0 -> ensures res=n;
}


int foo(int x)
 infer [x]
 requires true
 ensures res!=5;
{
  if (x<0) x=x-10;
  else x=x+10;
  x = abs(x);
  return x;
}

