data pair {
	int x;
	int y;
}
data quad {
	inline pair p1;
	pair p2;
}
int foo(pair q)
  requires q::pair<a,b>@L
  ensures res=a+b;
{
  return q.x+q.y;
}
