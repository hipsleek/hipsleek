int f(int x)
  infer [@term]
  //requires true
  //ensures true;
  case {
    x <= 0 -> requires Term ensures true;
    x > 0 -> requires Loop ensures false;
  }
{
  if (x <= 0) return 0;
  else return f(x) + g(x + 1);
}

int g(int x)
  infer [@term]
  requires true
  ensures true;
{
  if (x <= 0) return 0;
  else return f(x - 1) + f(x - 2);
}
