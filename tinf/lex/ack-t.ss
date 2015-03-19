template int r(int x, int y).

int Ack(int m, int n)
  infer [r]
  //requires m >= 0 & n >= 0 & Term[r(m, n)]
  //ensures res >= n + 1;
  
  case {
    m = 0 -> requires Term ensures res >= n + 1;
    m > 0 -> requires n >= 0 & Term[r(m, n)] ensures res >= n + 1;
  }
  
{
  if (m == 0) return n + 1;
  else if (n == 0) {
    return Ack(m - 1, 1);
  } else {
    int r = Ack(m, n - 1);
    return Ack(m - 1, r);
  }
}
