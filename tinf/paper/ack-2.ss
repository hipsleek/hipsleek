int Ack(int m, int n)
  infer [@term]
  requires true
  ensures (!(m >= 0 & n >= 0) | res >= 0);
{
  if (m == 0) return n + 1;
  else if (n == 0) {
    return Ack(m - 1, 1);
  } else {
    int r = Ack(m, n - 1);
    return Ack(m - 1, r);
  }
}
