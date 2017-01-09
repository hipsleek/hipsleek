struct pair {
	int x;
	int y;
};

struct quad {
	struct pair *p1;
	struct pair p2;
};

int getsecondcomponent(struct quad q)
{
	struct pair ptemp = {5,4};
	*(q.p1) = ptemp;
	ptemp = *(q.p1);
	struct pair pp = *(q.p1);
	
	struct pair *p;
	p->x = 1;
	p->y = 2;
	(*p).x = 2;
	
	return pp.y;
}

void main()
{
  return;
}

