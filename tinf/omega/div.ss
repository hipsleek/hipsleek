void foo(int x)
{
  if (x < 0) return;
  else foo(x/2);
}

void goo(int x)
{
  if (x <= 0) return;
  else goo(x/2);
}
