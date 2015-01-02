int main(int x)
  requires true
  ensures true;
{
  while (x > 0)
    infer [@post_n]
      requires true
      ensures true;
    {
      if (x > 2222) {
        break;
      } else {
        x = x - 1;
      }
    }
  return 0;
}

/*

With --en-split-fixcalc:

((x'=0 & 1<=x & x<=2222) | (x=x' & 2223<=x') | (x=x' & x'<=0))


Without --en-split-fixcalc:

x'<=x

*/
