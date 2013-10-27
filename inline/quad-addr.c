// inline fields

struct pair {
  int x;
  int y;
};

int foo(pair *q)
/*@
  requires *q::pair<a,b>@L
  ensures res=b;
*/
{
  return *q.y;
}

int mn()
/*@
  requires true
  ensures res=3;
*/
{
  pair p;
  p.y=3;
  foo(&p)
}


