int Ack(int m, int n)
  infer[@term]
  requires true
  ensures true;
{
  if (m == 0) return n + 1;
  else if (n == 0) return Ack(m-1, 1);
  else return Ack(m-1, Ack(m, n-1));
}
