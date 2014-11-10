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
      } else {
        x = x + 1;
      }
    }
  return 0;
}

/*

With --en-split-fixcalc:

((1<=x & x<=2000 & x'=2001) | (1998<=x & x<=2001 & x'=2001) | (x=x' & 2001<=x') | (x=x' & x'<=0))


Without --en-split-fixcalc:

((x'=2001 & x<=2000) | (x=x' & 2001<=x') | (x=x' & x'<=0))

*/
