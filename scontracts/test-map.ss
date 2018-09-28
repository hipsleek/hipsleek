hip_include 'scontracts/mapprimitives.ss'

int foo(mapping(int => int) mp)
   requires mp[0]=n
   ensures  res=n;
{
  int x = select(mp,0)[int,int];// mp[0];
  // int x = mp[0];
  return x;
}
