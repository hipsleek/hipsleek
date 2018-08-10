func int tf(int n) == ?.

int sum(int n)
  requires n >= 0 ensures res = n;

{
  if (tf(n) - 2 == 0) return n;
  else {
       return 1 + sum(n-1);
  }
}