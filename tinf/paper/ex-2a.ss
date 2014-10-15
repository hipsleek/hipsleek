void f(int x, int y)
  infer [@term]
  case {
    x < 0 -> requires true ensures true;
    x >= 0 -> requires true ensures true;
  }
{
  if (x < 0) return;
  else { 
    f(x + y, y);
  }
}