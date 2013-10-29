// partial fields

data pair {
	int x;
	int y;
}
data quad {
	inline pair p1;
	pair p2;
}

int poo(pair q)
  requires q::pair<a,#>
  ensures q::pair<a,#> & res=a;
{
  return q.x;
}

int foo(pair q)
  requires q.x::<a>
  ensures q.x::<a> & res=a;

{
  return q.x;
}

