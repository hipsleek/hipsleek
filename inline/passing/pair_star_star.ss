data pair {
  int x;
  int y;
}

data pair_star {
  pair deref;
}

data pair_star_star {
  pair_star deref;
}

int foo(pair_star_star p)
  requires p::pair_star_star<p1> * p1::pair_star<p2> * p2::pair<a,b>
  ensures p::pair_star_star<p1> * p1::pair_star<p2> * p2::pair<a+1,b> & res=a+1;
{
  int r = p.deref.deref.x + 1;
  p.deref.deref.x = r;
  return r;
}

int main()
  requires true
  ensures res=2;
{
  pair addr_p = new pair(1,1);
  pair_star addr_pp = new pair_star(null);
  addr_pp.deref = addr_p;
  pair_star_star addr_ppp = new pair_star_star(null);
  addr_ppp.deref = addr_pp;
  foo(addr_ppp);
  return addr_ppp.deref.deref.x;
}  
