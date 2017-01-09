int foo(int n)
 infer [@term]
 case {
  n>0 -> ensures res=n+1;
  n<=0 -> ensures res=n-1;
 }
{
  if(n>0)
  return n+1;
  else return n-1;
}

/*
# foo-fact2.ss

why isn't there an termination inference result here?
I am expecting:

 case {
  n>0 -> requires Term[] ensures res=n+1;
  n<=0 -> requires Term[] ensures res=n-1;
 }

*/
