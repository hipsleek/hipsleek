void f() {
  int x=0;
  int y=0;
  int *p = &y;

  //p = &x;
  //p = &x; // Just another mention of &x.
  *p = 1;
  int t = x;
  //@ dprint;
  //@ assert (y' = 0);
  //@ dprint;

  return;
}

void main()
{
  f();
}
