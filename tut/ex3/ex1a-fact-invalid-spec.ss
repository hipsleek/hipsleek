int fact (int n)
  requires Term[n] 
  ensures true;
{
  if (n == 0) return 1;
  else return n * fact(n - 1);
}
