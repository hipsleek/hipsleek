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
  int_star addr_x = new int_star(0); 
  addr_x.deref = 2;
  int r=foo(addr_x); // &x ==> addr_x
  return r;
}
/*
   if we detect int x, that &x is being used
   we transform as follows:
     int x   ==> int__star addr_x = new int__star(0) // stack allocate
     x = ..  ==> addr_x.deref = ..
     x       ==> addr_x.deref
     &x      ==> addr_x
*/


