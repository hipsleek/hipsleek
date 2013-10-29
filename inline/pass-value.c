// pass-by-value

struct pair {
  int x;
  int y;
};

/*
 data pair {
  int x;
  int y;
 }
*/

int foo(pair q)
// pass by copy
/*@
  requires q::pair<a,_>
  ensures q::pair<a,_> & res=a;
*/
{
  return q.x;
}

int foo2(pair q)
// pass by ptr
/*@
  requires q::pair<a,_>@L
  ensures res=a;
*/
{
  return q.x;
}


int goo(pair* q)
// pass by copy
/*@
  requires q::pair*<r> * r::pair<a,b>
  ensures q::pair*<r> * r::pair<a,b> & res=a;
*/
{
  return q->x;
}

int hoo() 
  requires true
  ensures res=5;
{
  pair p;
  p.x = 2; 
  int t=foo(p);
  pair* pp;
  pp = malloc(..);
  pp->x =3;
  t=t+goo(pp);
  return t;
}


