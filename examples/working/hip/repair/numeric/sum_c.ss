int sum(int n)
  requires n >= 0 ensures 2 * res = n * (n+1);

{
  if (n ==0) return 0;
  else {
       int m;
       m = sum(n-1);
       return n - m;
  }
}