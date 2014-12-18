int mc91(int n)
  case {
    n > 100 -> requires Term ensures res>=91;
    n <= 100 -> requires Term[100-n] ensures res>=91;
  }
{
  if (n > 100) return n-10;
  else return mc91(mc91(n+11));
}
