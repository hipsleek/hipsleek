int sumE(int n)
  infer[@term]
  case {
    exists (k: n=2*k) -> requires true ensures true;
    exists (k: n=2*k+1) -> requires true ensures true;
  }
{ 
  if (n==0) return 0;
  else return n+sumE(n-2);
}
