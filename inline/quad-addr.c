// addr-of operator

struct pair {
  int x;
  int y;
};

int foo(struct pair *q)
/*@
  requires q::pair<a,b>@L
  ensures res=b;
*/
{
  return (*q).y;
}

int main()
/*@
  requires true
  ensures res=3;
*/
{
  struct pair p;
  p.y=3;
  int r=foo(&p);
  return r;
}


