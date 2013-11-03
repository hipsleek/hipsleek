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
  ensures res=a+2;
*/
{
  int r = (*q).p1.x+1;
  r =0;
}

int main()
/*@
 requires true
  ensures res=5;
*/
{
  struct quad p;
  p.p1.x = 3;
  int rr=foo(&p);
  printf("p.p1.x = %i\n",p.p1.x); // 3
  printf("rr = %i\n",rr); //5
  return rr;

}


