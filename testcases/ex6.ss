data int_star {
  int v;
}

int_star foo()
{
  int_star addr_p = new int_star();
  addr_p.v = 1;
  int_star q = addr_p;

  return q;
}

int main()
{
  int_star a = foo();
  a.v = a.v; //simulate access to a.v that is required for printing in original
  return 0;
}