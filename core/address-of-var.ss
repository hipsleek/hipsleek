global int g;
global int* gptr;

void inc(int* i)
  requires i::int_ptr<v>
  ensures i::int_ptr<v+1>;
{
  (*i) = (*i) + 1;
}

void address_of_param(int x)
  requires true
  ensures true;
{
  x = 7;
  int* p = &x;
  inc(p);
  int z=x;
  assert (z'=8);//'
}

void address_of_local()
  requires true
  ensures true;
{
  int x = 7;
  int* p = &x;
  inc(p);
  int z=x;
  assert (z'=8);//'
}

void address_of_local2()
  requires true
  ensures true;
{
  int x = 7;
  int* ptr = &x;
  int** ptrptr;
  ptrptr = &ptr;
  inc(*ptrptr);
  int z = x;
  assert(z'= 8); //'
}

void address_of_global()
  requires true
  ensures true;
{
  g=7;
  int* p = &g;
  inc(p);
  int z=g;
  assert (z'=8);//'
}

void address_of_global2()
  requires true
  ensures true;
{
  g=7;
  gptr = &g;
  inc(gptr);
  int z=g;
  assert (z'=8);//'
}

void address_of_global3()
  requires true
  ensures gptr'::int_ptr<g'> & g'=8; //'
{
  g=7;
  gptr = &g;
  inc(gptr);
  int z=g;
  assert (z'=8);//'
}
