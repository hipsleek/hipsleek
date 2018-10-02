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


data node{
  int val;
}

int goo(mapping(int => int) mp)
   requires [n,m] mp[0]=n & mp[1]=m
   ensures  res=n+m;
{
  int x = mp[0]; // => select(mp,0)[int,int];
  int y = mp[1];
  return x+y;
}
