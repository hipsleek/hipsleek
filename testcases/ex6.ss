data int_star {
  int v;
}

int_star foo()
  requires emp
  ensures res::int_star<1>;
{
  int_star addr_p = new int_star();
  addr_p.v = 1;
  int_star q = addr_p;

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
