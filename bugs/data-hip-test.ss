data pair {
	int x;
	int y;
}

data quad {
	inline pair p1;
	pair p2;
}

int getsecondcomponent(quad q)
	requires q.p1.x::<a> * q.p1.y::<b> * q.p2::<c> * c::pair<_,_>
	ensures res = b;
{
	int k = q.p2.x;
	int h = q.p1.y;
	return q.p1.y;
}
