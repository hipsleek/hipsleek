void foo()
{
  int c = 2;
  int x;
  while ((x < c) || (x >= 0))
    requires c > 0
    case {
      x >=  c    -> requires Term[] ensures true;
      0 <= x < c -> requires Term[x] ensures true;
      x < 0      -> requires Term[] ensures true;
    }
  {
    x = x - c;
  }
}
