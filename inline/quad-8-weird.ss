//#include<stdio.h>
// inline fields

data pair {
  int x;
  int y;
}

data quad {
  inline pair p1;
  pair p2;
}


int rand() 
  requires true
  ensures true;

int foo(quad q)
  requires q::quad<a,b,p>@L
  ensures true;
{
  int r = q.p1.x+3;
  r =0;
  //return 0;
  // why did foo return (*q).p1.x+3?
  int tmp;
  return tmp;
}

int main()
 requires true
  ensures true;
{
  quad p = new quad(0,0,null);
  p.p1.x = 3;
  int rr=foo(p);
  //printf("p.p1.x = %i\n",p.p1.x); // 3
  //printf("rr = %i\n",rr); //5
  return rr;
  //p.p1.x = 3
  //rr = 6
}


