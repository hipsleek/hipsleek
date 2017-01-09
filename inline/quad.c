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
  ensures res=a;
*/
{
  return (*q).p1.x;
}


int foo3(struct quad* q)
/*@
  requires q::quad<a,b,p>@L
  ensures res=a;
*/
{
  struct quad* p=q;
  return (*q).p1.x;
}


void main()
{
  struct quad p;
  int x=foo(&p);
}

int foo4(struct quad q)
/*@
  requires q::quad<a,b,p>@L
  ensures res=a;
*/
{
  return q.p1.x;
}

