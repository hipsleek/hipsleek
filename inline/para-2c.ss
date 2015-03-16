//#include<stdio.h>
// addr-of operator
data pair {
  int x;
  int y;
}
data pair_star {
  pair deref;
}

int foo(pair@C q)
  requires q::pair<a,b>
  ensures q::pair<a+1+b,b> & res=a+1+b;
{
  pair_star addr_q = new pair_star(q);
  pair_star p = addr_q;
  pair_star p1 = addr_q;
  p.deref.x = addr_q.deref.x+1;
  p.deref.x = addr_q.deref.x+addr_q.deref.y ;
  return p.deref.x;
}

int main()
  requires true
  ensures res=1;
{
  pair p = new pair(0,0);
  p.x = 1;
  p.y = 2;
  int t=foo(p);
  //printf("foo(p) ==> %i\n",t); //4
  //printf("p.x ==> %i\n",p.x); //1
  return p.x;
}


