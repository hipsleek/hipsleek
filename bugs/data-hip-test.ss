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
	ensures res = 4;
{
	//q.p1.x = 0;
	
	//int k = q.p2.x;
	//int h = q.p1.y;

	pair ptemp = new pair(5,4);
	q.p1 = ptemp;
	ptemp = q.p1;

	return q.p1.y;
}
