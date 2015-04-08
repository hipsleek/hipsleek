void __error()
/*@
  requires emp & true
  ensures emp & true & flow __Error;
*/;

int sum(int n, int m)
/*@
  requires true
  ensures res=n+m;
*/
{
    if (n <= 0) {
      return m + n;
    } else {
      return sum(n - 1, m + 1);
    }
}

void main()
/*@
  requires true
  ensures true;
*/
{
  int a;
  int b;
  int result = sum(a, b);
  if (result != a + b) {
    __error();
  }
}
