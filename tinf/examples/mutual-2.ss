int f(int x)
  infer [@term]
  requires true
  ensures true;
{
  if (x <= 0) return 0;
  else return g(x + 1);
}

int g(int x)
  infer [@term]
  /*
  case {
    x <= 0 -> requires Term ensures true;
    x = 1 -> requires true ensures true;
    x > 1 -> requires true ensures true;
  }
  */
  requires true
  ensures true;
{
  if (x <= 0) return 0;
  else return f(x - 1);
}
