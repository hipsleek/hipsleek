void foo(int x, int c)
  requires c > 0
  case {
    x >=  c    -> requires Term[] ensures true;
    0 <= x < c -> requires Term[x] ensures true;
    x < 0      -> requires Term[] ensures true;
  }
{
  if ((x < c) && (x >= 0))
  {
    x = x - c;
    foo(x, c);
  }
}
