void f() {
  int x;
  int *p;

  p = &x;
  p = &x; // Just another mention of &x.
  *p = 0;
  //@ assert (x' = 0);

  return;
}

void main()
{
  f();
}
