data pair {
  int x;
  int y;
}

int foo(pair@C p)
  requires p::pair<a,b>
  ensures p::pair<#,#> & res=a+1;
{
  int r = p.x + 1;
  p = null;
  return r;
}

int main()
  requires true
  ensures res=2;
{
  pair p = new pair(1,1);
  foo(p);
  return p.x + 1;
}
