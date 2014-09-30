data pair {
	int x;
	int y;
}

data quad {
  pair p1;
	pair p2;
}


int foo()
{
  pair p1 = new pair(1,2);
  pair p2 = new pair(3,4);
  quad q = new quad(p1,p2);  
  //quad q = new quad((1,2),(3,4));
  int x = p1.x;
  return x;
}

void main()
{
  return;
}

