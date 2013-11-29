struct pair {
  int x;
  int y;
};

struct quad {
  struct pair* p1;
  struct pair p2;
};

int foo(struct quad q)
/*@
  requires q::quad<p,a,b> * p::pair<x,y>
  ensures q::quad<p,a,b> * p::pair<x+1,y> & res=x+1;
*/
{
  int r = q.p1.x + 1;
  q.p1.x = r;
  return r;
}

int main()
/*@
  requires true
  ensures res=1;
*/
{
  struct pair p1;
  p1.x = 0;
  p1.y = 0;
  struct pair p2;
  p2.x = 1;
  p2.y = 1;
  struct quad q;
  q.p1 = &p1;
  q.p2 = p2;
  foo(q);
  return q.p2.x;
}
