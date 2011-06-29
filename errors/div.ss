/*
int foo(int a, int b)
//requires b!=0
//ensures true;
 case {
  b=0 -> ensures true & flow __Error;
  b!=0 ->  ensures true;
 }
//ensures true;
{

  int x = a / b;
  return x;
}


int goo(int a, bool flag)
//requires true
//  ensures true & flow __flow;
//  requires true
//  ensures true & flow __norm;
 case {
   flag -> ensures res=a & flow __norm;
   !flag -> ensures true & flow __Error;
 }
{
  int x;
  if (flag) x = a/1;
  else x=a/0;
  return x;
}
*/
/*
int hoo(int a)
requires true & flow __Error
ensures true & flow __DivByZeroErr;
// requires true
//ensures true & flow __norm;
{
  int x;
  x = a/0;
  return x;
}
*/
int hoo1(int a)
requires true
ensures true & flow __Error;
// requires true
//ensures true & flow __norm;
{
  int x;
  x = a/0;
  return x;
}
