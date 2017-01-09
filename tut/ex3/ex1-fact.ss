int fact (int n)
  case {
    n >= 0 -> requires Term[n] ensures res > 0;
    n < 0 -> requires Loop ensures false;
  }
{
  if (n == 0) return 1;
  else return n * fact(n - 1);
}
