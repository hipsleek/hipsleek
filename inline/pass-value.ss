// pass-by-value
/*
struct pair {
  int x;
  int y;
};
*/

data pair {
  int x;
  int y;
 }

data pair_star {
  pair p;
}

void dispose()
  requires true
  ensures true;

int foo(pair@C q)
  requires q::pair<a,_>
  ensures q::pair<a,_> & res=a;
/*
  // for method declaration
  requires q::pair<a,_>
  ensures q::pair<a,_> & res=a;
  // for caller
  requires q::pair<a,_>@L
  ensures  res=a;
*/
{
  return q.x;
}
/*
int foo2(pair q)
  requires q::pair<a,_>@L
  ensures res=a;
{
  return q.x;
}

int goo(pair_star@C q)
  requires q::pair_star<r> * r::pair<a,b>
  ensures q::pair_star<r> * r::pair<a,b> & res=a;
/*
  // for method body
  requires q::pair_star<r> * r::pair<a,b>
  ensures q::pair_star<r> * r::pair<a,b> & res=a;
  // for callers
  requires q::pair_star<r>@L * r::pair<a,b>
  ensures  r::pair<a,b> & res=a;
*/
{
  return q->x;
}

int hoo() 
  requires true
  ensures res=5;
{
  pair p;
  p = new pair();
  p.x = 2; 
  int t=foo(p);
  pair_str pp;
  pp = new pair_star();
  pp.deref = new pair();
  pp.deref.x =3;
  t=t+goo(pp);
  dispose(pp); // to ensure no loss of stack object
  dispose(p); // to ensure no loss of stack object
  return t;
}

*/
