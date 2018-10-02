hip_include 'scontracts/mapprimitives.ss'

int foo(mapping(int => int) mp)
   requires true //mp[0]=n
   ensures  res=n;
{
  int x = mp[0]; // => select(mp,0)[int,int];
  //dprint;
  //mp[0]=9; // => update(mp,0,9)[int,int];
  //dprint;
  mapping(int => int) mp0;
  int y = mp0[0];
  //dprint;
  return x;
}
