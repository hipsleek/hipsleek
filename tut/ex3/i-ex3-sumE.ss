int sumE(int n)
  infer[@term]
  requires true
  ensures true;
{ 
  if (n==0) return 0;
  else return n+sumE(n-2);
}
