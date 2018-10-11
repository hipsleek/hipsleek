hip_include 'scontracts/mapprimitives.ss'

int foo(mapping(int => int) mp) // , mapping(int => int) mp9)
   requires [mp9] mp::Map<mp9> & Type(mp,mp9)
   ensures  res=9;
{
  mp[0] = 9; // => update(mp,0,9)[int,int];
  int x = mp[0];
  dprint;
  return x;
}


int foo1(mapping(int => int) mp)
   requires mp::Map<mp8> & Type(mp,mp8)
   ensures  res=14;
{
  mp[0] = 9; // => update(mp,0,9)[int,int];
  int x = mp[0];
  mp[0] = 5;
  dprint;
  return x + mp[0];
}


/*
R(mp1,mp2,key,val)  ==> (= (store mp1 key val) mp2)
*/
