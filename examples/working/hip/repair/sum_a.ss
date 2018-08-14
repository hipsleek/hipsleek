func int tf(int m) == ?.

int sum(int n)
  requires n >= 0 ensures 2 * res = n * (n+1);

{
  if (n ==0) return 0;
  else {
       int m, k;
       m = sum(n-1);
       k = tf(m);
       return n + k;
  }
}