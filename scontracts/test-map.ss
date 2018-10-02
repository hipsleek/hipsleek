hip_include 'scontracts/mapprimitives.ss'

int foo(mapping(int => int) mp)
   requires mp[0]=n
   ensures  res=n;
{
   int x = select(mp,0)[int,int];// mp[0];
   int y ;
   y = mp[0];
  //int x = 9;
  dprint;
  update(mp,0,9)[int,int];
  dprint;
  mapping(float => float) mp0;
  // int x = mp[0];
  dprint;
  return x;
}
