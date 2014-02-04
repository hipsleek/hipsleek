data int_star {
  int deref;
}

data int_star_star {
  int_star deref;
}

int foo(int_star_star q)
 requires q::int_star_star<r>*r::int_star<a>
 ensures q::int_star_star<r>*r::int_star<a> & res=0;
{
 q=null;
 return 0;
}

// this is wrong translation..
int foo2(int_star q)
 requires q::int_star<a>
 ensures q::int_star<a> & res=0;
{
 q=null;
 return 0;
}

int main()
 requires true
 ensures res=10;
{
 int_star addr_x = new int_star(10);
 int_star_star addr_r = new int_star_star(addr_x);
 foo(addr_r);
 int t = addr_r.deref.deref;
 return t;
}
