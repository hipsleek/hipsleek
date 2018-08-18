
int sum(int n)
  requires n >= 0 ensures res = (n * (n+1))/2;

{
  if (n ==0) return 2;
  else return n + sum(n-1);
}