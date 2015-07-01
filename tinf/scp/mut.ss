/*
void foo(ref int x, ref int y) 
  requires true
  ensures true;
{
  goo(x);
  //foo(x, y);
}

void goo(ref int z)
  //infer [@post_n]
  requires true
  ensures true;
{
  //hoo(z);
  foo(z, z);
  //hoo(z);
}

void hoo(ref int a)
  requires true
  ensures true;
{
  hoo(a);
}
*/

void g(int z)
  infer [@term]
  requires true
  ensures true;
{
  if (z <= 0) return;
  else g(f(z));
}

int f(int x)
  //infer [@post_n]
  requires true
  ensures true;
{
  int r = h(x - 1);
  return r;
}

int h(int y)
  infer [@post_n]
  requires true
  ensures true;
{
  return y + 1;
}
