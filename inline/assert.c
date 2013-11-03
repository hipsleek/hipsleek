void f() {
  int x=0;
  int *p;

  p = &x;
  p = &x; // Just another mention of &x.
  *p = 0;
  int t = x;
  //@ assert (x = 0);

  return;
}

void main()
{
  f();
}
