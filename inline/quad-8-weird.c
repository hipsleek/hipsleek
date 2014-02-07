#include<stdio.h>
// inline fields

struct pair {
  int x;
  int y;
};

struct quad {
  struct pair p1;
  struct pair* p2;
};

int foo(struct quad* q)
/*@
  requires q::quad<a,b,p>@L
  ensures res=0;
*/
{
  int r = (*q).p1.x+3;
  r =0;
  return 0;
  // why did foo return (*q).p1.x+3?
}

int main()
/*@
 requires true
  ensures res=0;
*/
{
  struct quad p;
  p.p1.x = 3;
  int rr=foo(&p);
  /*
  printf("p.p1.x = %i\n",p.p1.x); // 3
  printf("rr = %i\n",rr); //6 (random)
  printf("p.p1.y = %i\n",p.p1.y); //0 (random)
  printf("p.p2 = %i\n",p.p2); //4195264 (random)
  */
  return rr;
  //p.p1.x = 3
  //rr = 6
}
/*
p.p1.x = 3
rr = 6
p.p1.y = 0
p.p2 = 4195264
*/

