//#include<stdio.h>
// addr-of operator
data int_star {
  int deref;
}
data int_star_star {
  int_star deref;
}

int foo(int_star q)
  requires q::int_star<a>
  ensures q::int_star<a+1> & res=a+1;
{
  int_star_star addr_q = new int_star_star(q);
  int_star_star rr = addr_q;
  int_star r = rr.deref;
  rr.deref.deref = (rr.deref.deref)+1;
  return r.deref;
}

int main()
  requires true
  ensures res=3;
{
  int_star addr_x=new int_star(0);
  addr_x.deref=2;
  int t=foo(addr_x);
  //printf("foo(x) ==> %i\n",t);
  //printf("x ==> %i\n",addr_x.deref);
  return addr_x.deref;
}


