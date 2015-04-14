
void __error()
  requires  true
  ensures  true & flow __Error;

relation P(int a).

  relation Q(int a, int b).

void foo(int x)
//    requires x>10 ensures true & flow __Error;
infer [P] requires P(x) ensures true & flow __Error;
{
  while(x<10)
  case {
    x>10 -> ensures x'=x;
    x<=10 ->  ensures x'=10;
  }
    {
    x++;
  }
    assert (x' != 10);
    dprint;
    __error();
}
