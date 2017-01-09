void f(int x, int y, bool z)
  infer [@term]
  requires true
  ensures true;
{
  if (x < 0) return;
  else {
    if (z) f(x - y, y, z);
    else f(x + y, y, z);
  }
}
  
