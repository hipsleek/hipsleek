data int_star_star {
  int_star deref;
}
data int_star {
  int deref;
}

int foo(int_star_star@C q)
 requires q::int_star_star<r>*r::int_star<a>
//requires (exists r: q::int_star_star<r>*r::int_star<a>)
 ensures q::int_star_star<null>*r::int_star<a> & res=0;
{
  q.deref = null;
 return 0;
}

int main()
 requires true
 ensures true;
{
 int x;
 int_star addr_x = new int_star(x);
 int_star_star addr_r = new int_star_star(addr_x);
 //int* r = &x;
 foo(addr_r);
 return addr_x.deref;
}
