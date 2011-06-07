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
  //  x = div2(a,2);
  //x = div2(a,0);
  //int x = a / 2;
  //int x = div2(a,0);
  //x = div3(a,0);
  return x;
}


int goo(int a, bool flag)
//requires true
//  ensures true & flow __flow;
  requires true
  ensures true & flow __norm;
{
  int x;
  if (flag) x = a/1;
  else x=a/0;
  return x;
}

