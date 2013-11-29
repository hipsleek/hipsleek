//#include<stdio.h>
// addr-of operator
data pair {
  int x;
  int y;
}

data pair_star {
  pair deref;
}

int foo(pair q_ptr)
  requires q_ptr::pair<a,b>
  ensures q_ptr::pair<a+1+b,b> & res=a+1+b;
{
  pair_star addr_q = new pair_star(q_ptr);
  pair_star p = addr_q;
  p.deref.x = addr_q.deref.x+1;
  p.deref.x =  p.deref.x+ p.deref.y;
  return p.deref.x;
}

int main()
  requires true
  ensures res=4;
{
  pair addr_p = new pair(0,0); //stack allocate  
  addr_p.x = 1;
  addr_p.y = 2;
  int t=foo(addr_p);
  //printf("foo(p) ==> %i\n",t); //4
  //printf("p.x ==> %i\n",p.x); //4
  return addr_p.x;
}


