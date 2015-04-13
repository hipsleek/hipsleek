void __error()
  requires  true
  ensures  true & flow __Error;

relation P(int a).
relation Q(int a).


int foo(int n)
infer [P] requires P(n) ensures true & flow __Error;
//  requires n<3  ensures true & flow __Error;
{

  if (n < 3) {
    return 0;
  }
  else {
    foo(n-1);
    __error();
    return 1;
  }

 return 0;
}
