int fact (int n)
  requires Loop
  ensures false;
{
  if (n == 0) return 1;
  else return n * fact(n - 1);
}
