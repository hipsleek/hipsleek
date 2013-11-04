data int_star {
  int deref;
}

void f() {
  int x=0;
  int_star addr_x = new int_star(x);
  int_star p;

  p = addr_x;
  p = addr_x; // Just another mention of &x.
  p.deref = 1;
  int t = x;
  assert addr_x'::int_star<m> & m = 1;

  return;
}

void main()
{
  f();
}
