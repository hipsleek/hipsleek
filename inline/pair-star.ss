// two translation of pair*
data pair {
  int x;
  int y;
}

data pair_star {
   pair deref
}

int foo(pair_star@C q)
  requires q::pair_star<r>@L*pair<a,b>@L
  ensures res=b;
{
  return q.deref.y;
}


int star_foo(pair star_q)
  requires star_q::pair<a,b>@L
  ensures res=b;
{
  return star_q.y;
}

int mn()
  requires true
  ensures res=3;
{
  pair p;
  p = new pair(0,0);
  p.y=3;
  return star_foo(p);
}


