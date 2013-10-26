// inline fields

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

int goo(quad q)
  requires q::quad<a,b,p>
  ensures q::quad<a,b,p> & res=b;
{
  return q.p1.y;
}

int hoo(quad q)
  requires q::quad<a,b,p> * p::pair<c,d>
  ensures q::quad<a,b,p> * p::pair<c,d> & res=d;
{
  return q.p2.y;
}

int too(quad q)
  requires q.quad.p1.y::<b>
  ensures q.quad.p1.y::<b> & res=b;
{
  return q.p1.y;
}

int noo(quad q)
  requires q::quad<#,b,#>
  ensures q.quad.p1.y::<b> & res=b;
{
  return q.p1.y;
}

int roo(quad q)
  requires q::quad<#,b,#>
  ensures q::quad<a@A,b,#> & res=b;
{
  return q.p1.y;
}

