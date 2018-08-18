int sum(int n)
  requires n >= 0 ensures res = n * (n+1) * (n+2) /3;

{
  if (n ==0) return n;
  else return n*(n+1) + sum(n-1);
}