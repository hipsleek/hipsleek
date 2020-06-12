data int_star {
  int v;
}

data int_star_star {
  int_star v;
}

void free_is(int_star v)
  requires v::int_star<_>
  ensures  emp;

void free_iss(int_star_star v)
  requires v::int_star_star<_>
  ensures  emp;

void foo(int_star_star a)
  requires a::int_star_star<v>
  ensures a::int_star_star<v1> * v1::int_star<1>;
{
  int_star addr_b = new int_star();
  addr_b.v = 1;
  a.v = addr_b;
  free_is(addr_b);
}

int main()
  requires emp
  ensures res=1;
{
  //int_star c;
  //int_star s1 = new int_star();
  int_star_star addr_c = new int_star_star();
  foo(addr_c);
  int tmp2 = addr_c.v.v; // simulate access to *c that is required for printing in the original
  free_iss(addr_c);
  return tmp2;
}
