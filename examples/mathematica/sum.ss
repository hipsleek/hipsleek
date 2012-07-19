// sum from 0 to n
int sum(int n)
  requires n >= 0
  ensures res = n*(n+1)/2;
{
  if (n == 0) return 0;
  return sum_range(0,n);
}

// sum of first n odd number
int sum_odd(int n)
  requires n >= 1 
  ensures res = n*n;
{
  if (n == 1) return 1;
  int nth_odd = 2*n-1;
  return nth_odd + sum_odd(n-1);
}

// sum from n to m
int sum_range(int n, int m) 
  requires n <= m
  ensures res = (m*m - n*n + m + n)/2;
{
  if (n == m) return n;
  return n + sum_range(n+1, m);
  // return m + sum_range(n, m-1);
}

// sum from 0 to n = 2*k+1
int sum_to_odd(int k)
  requires k >= 0
  ensures res = (k+1)*(2*k+1);
{
  if (k == 0) return 1;
  return (2*k+1) + 2*k + sum_to_odd(k-1);
}
