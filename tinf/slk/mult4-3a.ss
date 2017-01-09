void f(int x, int y, int z)
  infer [@term]
  requires true
  ensures true;
{
  if (x < 0) return;
  else {
    if (z >= 0) f(x - y, y, z);
    else f(x + y, y, z);
  }
}
  
