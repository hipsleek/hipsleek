int id(int x)
  requires true
  ensures res=x+1 & res<?x;
{
  dprint;
  int y = x + 1;
  dprint;
  return y;
  dprint;
}
