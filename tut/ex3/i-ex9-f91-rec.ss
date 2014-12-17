int mc91(int n)
  infer[@term]
  requires true
  ensures true;
{
  if (n > 100) return n-10;
  else return mc91(mc91(n+11));
}
