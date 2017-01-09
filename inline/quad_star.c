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
  return q->p1.x;
}

int foo2(struct quad *q)
/*@
  requires q::quad<a,b,p>@L
  ensures res=a;
*/
{
  return (*q).p1.x;
}

//foo(q) ==> star_foo(*q)

int star_foo(struct quad star_q)
/*@
  requires star_q::quad<a,b,p>@L
  ensures res=a;
*/
{
  return star_q.p1.x;
}


