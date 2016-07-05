data pair {
	int x;
	int y;
}

data quad {
	inline pair p1;
	pair p2;
}

int getsecondcomponent(quad q)
{
	pair ptemp = new pair(5,4);
	q.p1 = ptemp;
	ptemp = q.p1;
  pair pp = q.p1;
	return pp.y;
}

void main()
{
  return;
}

