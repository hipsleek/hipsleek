int fact(int x)
  infer [@term]
  requires true
  ensures res >= 1;
{
  if (x==0) return 1;
  else return 1 + fact(x - 1);
}
