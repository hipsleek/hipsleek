hip_include 'scontracts/mapprimitives.ss'


int foo(mapping(int => int) mp)
   requires mp[0]=n
   ensures  res=n;
{
  //mapping(int=>int) mp0;
  dprint;
  int x = select(mp,0)[int,int];// mp[0];
  // int x = mp[0];
  return x;
}

/*
`T1 foo [T1,T2] (`T2 x, int y)
  requires true
  ensures  true;

void goo()
  requires true
  ensures  true;
{
  int x = foo(1,2)[int,int];
}
*/
