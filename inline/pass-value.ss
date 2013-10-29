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
  pair deref;
}

void dispose()
  requires true
  ensures true;

int foo(pair@C q)
  requires q::pair<a,_>
  ensures q::pair<a,5> & res=a;
/*
  // for method declaration
  requires q::pair<a,_>
  ensures q::pair<a,5> & res=a;
  // for caller
  requires q::pair<a,_>@L
  ensures  res=a;
*/
{
  q.y=5;
  return q.x;
}

pair foo_test()
  requires true
  ensures res::pair<1,6>;
{
  pair p=new pair(0,6);
  p.x=foo(p)+1;
  return p;
}

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
  return q.deref.x;
}

int hoo() 
  requires true
  ensures res=5;
{
  pair p;
  p = new pair(0,0);
  p.x = 2; 
  int t=foo(p);
  pair_star pp;
  pp = new pair_star(p);
  pp.deref = new pair(0,0);
  pp.deref.x =3;
  t=t+goo(pp);
  //  dispose(pp); // to ensure no loss of stack object
  //dispose(p); // to ensure no loss of stack object
  return t;
}


