// inline fields

struct pair {
  int x;
  int y;
};

struct quad {
  struct pair p1;
  struct pair* p2;
};

int foo(quad *q)
/*@
  requires q^::quad<a,b,p>@L
  ensures res=a;
*/
{
  return (*q).p1.x;
}


int foo3(quad* q)
/*@
  requires q^::quad<a,b,p>@L
  ensures res=a;
*/
{
  quad* q;
  quad* p=q;
  /*@ assert p=q */ 
  /*@ assert &p=&q */ 
  return (*q).p1.x;
}


void main()
{
  struct quad p;
  int x=foo(&p);
}

int foo(quad q)
/*@
  requires q::quad<a,b,p>@L
  ensures res=a;
*/
{
  return q->p1.x;
}

