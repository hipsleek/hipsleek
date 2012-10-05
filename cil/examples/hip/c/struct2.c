struct pair {
	int x;
	int y;
  int ***aa;
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
	return pp.y;
}

void main()
{
  return;
}

