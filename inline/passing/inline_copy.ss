data pair {
  int x;
  int y;
}

data quad {
  pair p1;
  inline pair p2;
}

int foo(quad@C q)
  requires q::quad<p,a,b> * p::pair<x,y>
  ensures q::quad<p,a+1,b> * p::pair<x,y> & res=a+1;
{
  int r = q.p2.x + 1;
  q.p2.x = r;
  return r;
}

int main()
  requires true
  ensures res=1;
{
  pair p1 = new pair(0,0);
  pair p2 = new pair(1,1);
  quad q = new quad(p1,p2.x,p2.y);
  foo(q);
  return q.p2.x;
}
