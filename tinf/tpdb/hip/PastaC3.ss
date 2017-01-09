void f(int x, int y, int z)
  infer [@term]
  requires true
  ensures true;
{
  while (x < y) 
    infer [@term]
    requires true
    ensures true;
  {
    if (x < z) {
      x++;
    } else {
      z++;
    }
  }
}
