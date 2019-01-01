
int sum(int n)
  requires n >= 0
  ensures 2 * res = n * (n+1);

{
  int z = 1;
  int x = 2;
  if (n ==0) return 0;
  else {
    z=z+1;
    int t = sum(n-1);
    x=x+2;
    int a = n+t;
    return a;
  }
}
