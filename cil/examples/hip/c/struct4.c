struct pair {
	int x;
	int y;
};

int foo()
{
	struct pair *p;
	p->x = 1;
	p->y = 2;
	return 1;
}

void main()
{
  return;
}

