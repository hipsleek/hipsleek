data int_star {
  int v;
}

void free_is(int_star v)
  requires v::int_star<_>
  ensures  emp;

int_star foo()
  requires emp
  ensures res::int_star<1>;
{
  int_star addr_p = new int_star();
  addr_p.v = 1;
  int_star q = addr_p;
  free_is(addr_p);
  /* stack allocated memory needs to be
    ..automatically deallocated
    Is there a generic free? What is best way to
    implement it?
  */
  return q;
}

int main()
  requires emp
  ensures res=0;
{
  int_star a = foo();
  a.v = a.v; //simulate access to *a that is required for printing in original
  return 0;
}
