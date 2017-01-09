int main(int x)
  requires true
  ensures true;
{
  while (x > 0)
    infer [@post_n]
      requires true
      ensures true;
    {
      if (x > 2000) {
        break;
      } else if (x > 1000 && x <= 2000) {
        x = x + 1;
      } else if (x > 0 && x <= 1000) {
        x = x - 1;
      }
    }
  return 0;
}

/*

With --en-split-fixcalc:

((x'=0 & 1<=x & x<=2000) | (x'=2001 & 1<=x & x<=2000) | (x=x' & 2001<=x') | (x=x' & x'<=0))


Without --en-split-fixcalc:

true

*/
