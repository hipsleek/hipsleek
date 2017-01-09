void f()
  infer [@term]
  requires true
  ensures true;
{
  int x, y, z;
  while (x < y) 
    infer [@term]
    requires true
    ensures true;
  {
    x--;
  }
}
