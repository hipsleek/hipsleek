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
  requires q::quad<a,b,p>@L
  ensures res=a+2;
{
  int r = q.p1.x+2;
  return r;
}



int main()
 requires true
  ensures res=5;
{
  quad p = new quad(0,0,null); //stack alloc
  p.p1.x = 3;
  int r=foo(p);
  return r;
}
