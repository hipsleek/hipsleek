int mc91(int n)
  infer[@term]
  requires true 
  ensures true;
{
  int c = 1;
  while (c > 0)
    infer[@term]
    requires true 
    ensures true;
  {
    if (n > 100) {
      n = n - 10;
      c = c - 1;
    } else {
      n = n + 11;
      c = c + 1;
    }
  }
  return n;
}
