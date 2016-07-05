//#include<stdio.h>
// addr-of operator
data pair {
  int x;
  int y;
}

int foo(pair q_ptr)
  requires q_ptr::pair<a,b>
  ensures q_ptr::pair<a+1+b,b> & res=a+1+b;
{
  q_ptr.x = q_ptr.x+1;
  q_ptr.x = q_ptr.x+q_ptr.y;
  return q_ptr.x;
}

int main()
  requires true
  ensures res=4;
{
  pair p = new pair(0,0);
  p.x = 1;
  p.y = 2;
  int t=foo(p);
  //printf("foo(p) ==> %i\n",t); //4
  //printf("p.x ==> %i\n",p.x); //4
  return p.x;
}


