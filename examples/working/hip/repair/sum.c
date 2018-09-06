int sum(int n)
/*@
  requires n >= 0 ensures res = n * (n+1)/2;
*/
{
  if (n == 0) return 0;
  //if (n ==0) return 0;
  else {
    int m;
    m = n - 2;
    return n + sum (m);
  }
}
