data pair {
	int x;
	int y;
}
data quad {
	inline pair p1;
	pair p2;
}
int foo(quad q)
  requires q::quad<a,b,p>@L
  ensures res=a;
{
  return q.p1.x;
}
