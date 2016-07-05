data pair {
  int x;
  int y;
}

data pair_star {
  pair deref;
}

int foo(pair_star p)
  requires p::pair_star<r> * r::pair<a,b>
  ensures p::pair_star<r> * r::pair<a+1,b> & res=a+1;
{
  int r = p.deref.x + 1;
  p.deref.x = r;
  return r;
}

int main()
  requires true
  ensures res=2;
{
  pair addr_p = new pair(1,1);
  pair_star pp = new pair_star(null);
  pp.deref = addr_p;
  foo(pp);
  return pp.deref.x;
}

int foo1(pair p)
  requires p::pair<a,b>
  ensures p::pair<a+1,b> & res=a+1;
{
  int r = p.x + 1;
  p.x = r;
  return r;
}

int main1()
  requires true
  ensures res=2;
{
  pair p = new pair(1,1);
  foo1(p);
  return p.x;
}
