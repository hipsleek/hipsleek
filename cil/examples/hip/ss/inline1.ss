data pair {
	int x;
	int y;
}

data quad {
	inline pair p1;
	pair p2;
}

int getsecondcomponent()
{

	pair pp1 = new pair(5,4);
	pair pp2 = new pair(6,7);
	quad q = new quad(pp1, pp2);
	q1.p1 = pp2;
	return q1.p1.x;
}

