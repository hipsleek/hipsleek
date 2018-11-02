hip_include 'scontracts/mapprimitives.ss'

/** Should fail */
int foo( mapping(int => int) mp)
   requires mp::Map<mp9>@L
   ensures  res=9;
{
  mp[0] = 9; // => update(mp,0,9)[int,int];
  int x = mp[0];
  dprint;
  return x;
}


int foo1(mapping(int => int) mp)
   requires  mp::Map<mp8>
   ensures   (exists mp9: mp::Map<mp9> & res=14);
{
  mp[0] = 9; // => update(mp,0,9)[int,int];
  int x = mp[0];
  mp[0] = 2;
  mp[0] = 5;
  dprint;
  return x + mp[0];
}

int foo11(ref mapping(int => int) mp)
   requires  mp::Map<mp8>
   ensures   (exists mp9: mp'::Map<mp9> & res=14 & mp9[0]=5);
{
  mp[0] = 9; // => update(mp,0,9)[int,int];
  int x = mp[0];
  mp[0] = 2;
  mp[0] = 5;
  dprint;
  return x + mp[0];
}

/**
below fails as the instantiations can't discover mp9
*/
void foo2(ref mapping(int => int) mp)
   requires  [mp9] mp::Map<mp8>
   ensures   mp'::Map<mp9> & mp9[0]=5;
{
  mp[0] = 5;
  dprint;
}


/* below succeeds */
void foo3(ref mapping(int => int) mp)
   requires   mp::Map<mp8>
   ensures   (exists mp9: mp'::Map<mp9> & mp9[0]=5);
{
  mp[0] = 5;
  dprint;
}

/* below succeeds */
void foo4(ref mapping(int => int) mp)
   requires   mp::Map<mp8>
   ensures   (exists mp9: mp'::Map<mp9> & mp9[0]=5);
{
  mp[0] = 2;
  mp[0] = 5;
  dprint;
}



/*
R(mp1,mp2,key,val)  ==> (= (store mp1 key val) mp2)
*/
