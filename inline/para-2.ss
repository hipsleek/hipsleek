//#include<stdio.h>
// addr-of operator
data int_star {
  int deref;
}

int foo(int_star q)
  requires q::int_star<a>
  ensures q::int_star<a+1> & res=a+1;
{
  int_star r = q;
  r.deref = (r.deref)+1;
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


