void f() {
  int x=0;
  int y=0;
  int *p = &y;

  //p = &x;
  //p = &x; // Just another mention of &x.
  *p = 0;
  int t = x;
  //@ dprint;
  //@ assert (x' = 0);
  //@ dprint;

  return;
}

void main()
{
  f();
}
