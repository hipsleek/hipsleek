struct point
{
  int x;
};

int foo()
{
  struct point p = {1};
  return p.x;
}

void main()
{
  return;
}
