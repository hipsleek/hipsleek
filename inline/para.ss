//#include<stdio.h>
// addr-of operator
data int_star {
  int deref;
}

int foo(int q)
  requires true
  ensures res=q+1;
{
  int_star addr_q = new int_star(q);
  int_star r = addr_q;
  r.deref = (r.deref)+1;
  return r.deref;
}

int main()
  requires true
  ensures res=2;
{
  int x;
  x=2;
  int t=foo(x);
  //printf("foo(x) ==> %i\n",t); ==>3
  //printf("x ==> %i\n",x); ==>2
  return x;
}


