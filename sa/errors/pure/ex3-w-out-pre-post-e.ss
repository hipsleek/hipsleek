
void __error()
  requires  true
  ensures  true & flow __Error;

relation P(int a).
relation Q(int a, int b).

int foo(int x)
//  infer [P,Q] requires P(x) ensures Q(x,res);
   infer [P,Q] requires P(x) ensures true & flow __Error;
{
  if (x<10){
    x=x+1;
    int tmp = foo(x);
    __error();
    return tmp;
  }

  return x;
}
