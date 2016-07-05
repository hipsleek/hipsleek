//#include<stdio.h>
// addr-of operator
data pair {
  int x;
  int y;
}

int foo(pair@C q)
  requires q::pair<a,b>
  ensures q::pair<a+1,b> & res=a+1+b;
{
  pair p = new pair(q.x,q.y);
  q.x=q.x+1;
  p.x = q.x+q.y;
  return p.x;
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


