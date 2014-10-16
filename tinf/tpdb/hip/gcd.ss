void gcd (int a, int b)

{
  if (a == b) return;
  else if (a > b) gcd(a - b, b);
  else gcd(a, b - a);
}
