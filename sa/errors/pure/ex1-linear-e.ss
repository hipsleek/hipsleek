void __error()
  requires  true
  ensures  true & flow __Error;

relation P(int a).
relation Q(int a).


int foo(int n)
//infer [P] requires P(n) ensures res=1 & flow __Error;
  requires n<3  ensures res=1 & flow __Error;
{

 assume n < 3;
  dprint;
 __error();

 dprint;

 return 0;
}
