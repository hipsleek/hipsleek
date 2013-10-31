data pair {
  int x;
  int y;
}

int foo(pair@C p)
  requires p::pair<a,b>
  ensures p::pair<a+1,b> & res=a+1;
{
  int r = p.x + 1;
  p.x = r;
  return r;
}

int main()
  requires true
  ensures res=1;
{
  pair p = new pair(1,1);
  foo(p);
  return p.x;
}
