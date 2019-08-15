func int tf() == ?.

int sum(int n)
  requires n >= 0 ensures 2 * res = n * (n+1);

{
  if (n ==0) return tf();
  else {
       return n + sum(n - 1);
  }
}