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

int fact(int x)
 infer [@term] requires true  ensures true;
/*
 case {
   x<0 -> requires Loop ensures false;
   x=0 -> requires Term[] ensures true;
   x>0 -> requires Term[x] ensures true;
 }
*/
//  requires true  ensures Uf(x,res);
//  requires true ensures res=x;
{
  if (x==0) return 1;
  else return foo(1) + fact(x - 1);
}
/*
# foo-fact1.ss

This should work after you fix foo-fact2.ss
It should print two term inference results.

*/
