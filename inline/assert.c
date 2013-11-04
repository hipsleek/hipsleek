void f() {
  int x=0;
  int *p;

  p = &x;
  p = &x; // Just another mention of &x.
  *p = 1;
  int t = x;
  //@ assert (x = 1);

  return;
}

void main()
{
  f();
}
