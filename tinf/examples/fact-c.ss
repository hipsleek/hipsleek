int fact(int x)
  infer [@term]
  case {
    x = 0 -> requires Term[] ensures res >= 1;
    x != 0 -> requires true ensures res >= 1;
  }
{
  if (x==0) return 1;
  else return 1 + fact(x - 1);
}