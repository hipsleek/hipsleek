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
// pass by value
/*@
  requires q::pair<a,_>@S
  ensures q::pair<a,_>@S & res=a;
*/
{
  return q.x;
}

int goo(pair* q)
// pass by value
/*@
  requires q::pair*<r>@S * r::pair<a,b>
  ensures q::pair*<r>@S * r::pair<a,b> & res=a;
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


