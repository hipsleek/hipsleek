void f(int x, int y)

  infer [@term]
  requires true
  ensures true;
/*
  case {
    x <= 0 -> requires Term ensures true;
    x > 0 -> case {
      y >= 0 -> requires Term[2*x + 2*y + 1] ensures true;
      y < 0 -> requires Term[2*x] ensures true;
    }
  }
*/
{
  if (x <= 0) return;
  else f(x + y, -1 - y);
}