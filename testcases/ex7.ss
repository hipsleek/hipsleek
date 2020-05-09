data int_star {
  int v;
}

data int_star_star {
  int_star v;
}

void foo(int_star_star a)
  requires a::int_star_star<v>
  ensures a::int_star_star<v1>;
{
  int_star addr_b = new int_star();
  a.v = addr_b;
}

int main()
{
  int_star c;
  int_star_star addr_c = new int_star_star(c);
  foo(addr_c);
  addr_c.v.v = addr_c.v.v; // simulate access to *c that is required for printing in the original
}