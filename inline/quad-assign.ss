// assignment for struct p=q.p1 works!

data pair {
  int x;
  int y;
}

data quad {
  inline pair p1;
  pair p2;
}

int foo(quad q)
  requires q::quad<a,b,p>
  ensures q::quad<a,b,p> & res=b;
/*
  requires q::quad<a,b,p>@L
  ensures  res=a;
*/
{
  pair p;
  p = new pair(0,5); // stack allocate
  p = q.p1;
  //above is equivalent to:
  //p.x = q.p1.x;
  //p.y = q.p1.y;
  int rs = p.y;
    //dispose(p)
  return rs;
}



