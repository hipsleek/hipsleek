// inline fields

data pair {
	int x;
	int y;
}
data quad {
	inline pair p1;
	pair p2;
}
data quad__star {
  quad deref;
}

/*
    
 */
int foo(quad q)
  requires q::quad<a,b,p>@L * p::pair<c,d>@L
  ensures res=c+2;
{
  int r = q.p2.x+2;
  return r;
}



int main()
 requires true
  ensures res=6;
{
  quad p = new quad(0,0,null); //stack alloc
  pair pp = new pair();
  pp.x=4;
  p.p2 = pp;
  p.p1.x = 3;
  int r=foo(p);
  return r;
}
