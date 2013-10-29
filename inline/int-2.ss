data int_star {
  int deref;
}

// addr-of operator
int foo(int_star q)
  requires q::int_star<a>
  ensures q::int_star<a+1> & res=a+1;
{
  int r = (q.deref)+1;
  q.deref = r;
  return r;
}

int main()
  requires true
  ensures res=3;
{
  int_star addr_x = new int_star(0);
  addr_x.deref=5;
  int_star r = addr_x;
  addr_x.deref=2;
  int t=foo(r);
  int k=addr_x.deref+1;
  return addr_x.deref;
}


