// addr-of operator

data int_star {
  int deref;
}

int foo(int_star q)
  requires q::int_star<a>
  ensures  q::int_star<a+1> & res=a+1;
{
  int r = q.deref+1;
  q.deref = r;
  return r;
}

int main()
  requires true
  ensures res=3;
{
  // using addr_x for &x
  int_star addr_x = new int_star(0); 
  addr_x.deref = 2;
  int r=foo(addr_x); // &x ==> addr_x
  return r;
}


