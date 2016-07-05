// removing addr-of operator
data pair {
  int x;
  int y;
}

/*
int foo(pair *q)
  requires *q::pair<a,b>@L
  ensures res=b;
{
  return *q.y;
}
*/

int star_foo(pair star_q)
  requires star_q::pair<a,b>@L
  ensures res=b;
{
  return star_q.y;
}

void dispose(pair p)
  requires p::pair<_,_>
  ensures true;

int main()
  requires true
  ensures res=3;
{
  pair p;
  p = new pair(0,0); // stack allocation
  p.y=3;
  int r=star_foo(p); // *(&p) ==> p
  dispose(p);
  return r; 
}


