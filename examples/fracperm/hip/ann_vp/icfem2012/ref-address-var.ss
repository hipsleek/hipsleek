/*
  Example of addressable reference parameters
 */

void inc(ref int x,int y)
  requires true
  ensures x'=x+y; //'
{
  x=x+y;
}

void main()
  requires true
  ensures true;
{
  int x = 7;
  int y=0;
  int* ptr = &x;
  int id = fork(inc,x,y+1);
  //any accesses to x or *p are racy (unsafe)
  join(id);
  int z = x;
  assert(z'= 8); //'
}

void main2()
  requires true
  ensures true;
{
  int x = 7;
  int y=0;
  int* ptr = &x;
  int id = fork(inc,x,y+1);
  int z2 = *ptr; // fail because the pseudo-heap location
  // was captured by the child thread
  join(id);
  int z = x;
  assert(z'= 8); //'
}
