struct pair {
	int x;
	int y;
};

int foo()
{
	struct pair *p;
	(p+1)->x = 1;
	(p+2)->y = 2;
	return 1;
}

void main()
{
  return;
}

