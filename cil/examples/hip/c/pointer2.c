struct point
{
  int x;
};


int foo()
{
  struct point p = {3};
  int *zzz;
  *zzz = 1;
//  *(zzz+2)=4;
  zzz = 2;
  return *zzz;
}

void main()
{
}
