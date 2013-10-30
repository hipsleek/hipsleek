// inline fields

struct pair {
  int x;
  int y;
};

struct quad {
  struct pair p1;
  struct pair* p2;
};

int foo(struct quad q)
/*@
  requires q::quad<a,b,p>@L
  ensures res=a;
*/
{
  struct pair p;
  p = q.p1;
  return p.x;
}



