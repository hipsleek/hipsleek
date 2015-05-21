
void __error()
  requires  true
  ensures  true & flow __Error;

relation P(int a).

relation P1(int a).
  relation Q(int a, int b).

void foo(int x)
//    requires x>10 ensures true & flow __Error;
infer [P] requires P(x) ensures true & flow __Error;
{
  // x=0;
  while(x<10)
    /*
      case {
      x>10 -> ensures x'=x;
      x<=10 ->  ensures x'=10;
      }
    */
    requires true ensures ((9>=x & x'=10) | (x>=10 & x'=x));
    //infer [P1,Q] requires P1(x) ensures Q(x,x');
    {
    x = x + 1;
  }
    //  dprint;
    assert (x' != 10);
   __error();
}
