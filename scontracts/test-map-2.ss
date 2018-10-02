hip_include 'scontracts/mapprimitives.ss'

int foo(mapping(int => int) mp)
   requires true //mp[0]=n
   ensures  res=n;
{
  int x = mp[0];
  mapping(int => int) mp0;
  int y = mp0[0];
  dprint;
  return x;
}


data node{
  int val;
}

int goo(mapping(int => node) mp)
   requires [p,q,n,m]
             p::node<n>*q::node<m> & mp[0]=q & mp[1]=p
   ensures  res=n+m;
{
  node x = mp[0]; // => select(mp,0)[int,int];
  node y = mp[1]; //mp[1].val; !! parse error
  return x.val + y.val;
}

/*
TODO: solve the parsing error
int goo0(mapping(int => node) mp)
   requires [p,q,n,m]
             p::node<n>*q::node<m> & mp[0]=q & mp[1]=p
   ensures  res=n+m;
{
  int x = mp[0].val; //mp[1].val; !! parse error
  int y = mp[1].val; //mp[1].val; !! parse error
  return x+y;
}
*/
