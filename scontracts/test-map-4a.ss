hip_include 'scontracts/mapprimitives.ss'

global mapping(int => int) mp;

/** FAIL - ok*/
int foo()
   requires mp::Map<mp9>@L
   ensures  res=9;
{
  mp[0] = 9;
  int x = mp[0];
  dprint;
  return x;
}

/* SUCCESS - ok */
int foo1()
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

/* SUCCESS - ok */
int foo11()
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
void foo2()
   requires  [mp9] mp::Map<mp8>
   ensures   mp'::Map<mp9> & mp9[0]=5;
{
  mp[0] = 5;
  dprint;
}


/* SUCCESS - ok */
void foo3()
   requires   mp::Map<mp8>
   ensures   (exists mp9: mp'::Map<mp9> & mp9[0]=5);
{
  mp[0] = 5;
  dprint;
}

/* SUCCESS - OK */
void foo4()
   requires   mp::Map<mp8>
   ensures   (exists mp9: mp'::Map<mp9> & mp9[0]=5);
{
  mp[0] = 2;
  mp[0] = 5;
  dprint;
}

/* FAILS - OK */
void foo5()
   requires   mp::Map<mp8>
   ensures   (exists mp9: mp'::Map<mp9> & mp9[0]=2);
{
  mp[0] = 2;
  mp[0] = 5;
  dprint;
}

global int yyy;

/** SUCCESS - ok*/
int foo6()
   requires mp::Map<mp9>@L & mp9[0]=9
   ensures  res= 9 + yyy;
{
  int x = mp[0];
  dprint;
  return x + yyy;
}

/** SUCCESS - ok*/
int foo7()
   requires mp::Map<mp9>@L
   ensures  res= 9 + yyy;
{
  int x;
  if (mp[0] == 9){
     x = mp[0];
  } else {
     x = 9;
  }
  return x + yyy;
}

/** SUCCESS - ok*/
int foo8()
   requires mp::Map<mp9>@L
   ensures  res = 9 + yyy;
{
  int x;
  if (mp[0] == 9){
     x = mp[0];
  } else {
     x = 9;
  }
  dprint;
  return x + yyy;
}


/** SUCCESS - ok*/
int foo9()
   requires mp::Map<mp9>
   ensures  (exists mp1: mp'::Map<mp1> & mp1[0]=9);
{
  int x;
  if (mp[0] == 9){
     x = mp[0];
  } else {
     mp[0] = 9;
     x = mp[0];
  }
  dprint;
  return x + yyy;
}

/** SUCCESS - ok*/
int foo10()
   requires mp::Map<mp9> & mp9[0]=0
   ensures  (exists mp1: mp'::Map<mp1> & mp1[0]=9 & mp9[0]=0);
{
  int x;
  if (mp[0] == 9){
     x = mp[0];
  } else {
     mp[0] = 9;
     x = mp[0];
  }
  dprint;
  return x + yyy;
}



/** SUCCESS - ok*/
int foo13()
   requires mp::Map<mp9> & mp9[0]>=0
   ensures  (exists mp1: mp'::Map<mp1> & mp1[0]=9 & res = yyy+9);
{
  int x;
  mp[0] = mp[0] + 1;
  if (mp[0] == 9){
     x = mp[0];
  } else {
     mp[0] = 9;
     x = mp[0];
  }
  dprint;
  return x + yyy;
}

/** FAIL - ok due to res */
int foo14()
   requires mp::Map<mp9> & mp9[0]>=0
   ensures  (exists mp1: mp'::Map<mp1> & mp1[0]=9 & res = 9);
{
  int x;
  mp[0] = mp[0] + 1;
  if (mp[0] == 9){
     x = mp[0];
  } else {
     mp[0] = 9;
     x = mp[0];
  }
  dprint;
  return x + yyy;
}


//lemma_norm self::Mappp<> & self[x]=y -> self::Map<mp111> & mp111[x]=y.
//lemma_norm self::Mappp<> -> self::Map<mp111> & mp111=self.

/** FAIL - not ok*/
/*
void foo12()
   // requires mp::Map<mp9> & mp9[0]=0
   // ensures  (exists mp1: mp'::Map<mp1> & mp1[0]=9 );
   requires mp::Mappp<> & mp[0]=0
   ensures  mp'::Mappp<> & mp'[0]=9;
{
  int x;
  dprint;
  mp[0] = 9;
  dprint;
}
*/

/***************************************/

data address {
     int id;
}

global mapping(address => int) userBalances;

/**SUCCESS - ok*/
void foo16(address id)
   requires   [ub] userBalances::Map<ub> & ub[id]=n & n>0
   ensures   (exists ub0: userBalances'::Map<ub0> & ub0[id]=0);
{
  userBalances[id] = 0;
}


/**FAIL - ok*/
void foo17(address id)
   requires   [ub] userBalances::Map<ub> & ub[id]=n & n>0
   ensures   (exists ub0: userBalances'::Map<ub0> & ub0[id]=10);
{
  userBalances[id] = 0;
}


/**SUCCESS - ok*/
void foo18(address id)
   requires   [ub] userBalances::Map<ub> & ub[id]=n & n>0
   ensures   (exists ub0: userBalances'::Map<ub0> & ub0[id]=10);
{
  userBalances[id] = 0;
  userBalances[id] = 10;
}


/**SUCCESS - ok*/
int foo19(address id)
   requires   [ub] userBalances::Map<ub>
   ensures   (exists ub0: userBalances'::Map<ub0> & ub0[id]>=0 & res = ub0[id]);
{
  if (userBalances[id] > 0 ) return userBalances[id];
  else {
    userBalances[id] = 0;
    return userBalances[id];
  }
}


/**SUCCESS - ok*/
int foo20(address id)
   requires   [ub] userBalances::Map<ub>
   ensures   (exists ub0: userBalances'::Map<ub0> & res>=0 & res = ub0[id]);
{
  if (userBalances[id] > 0 ) return userBalances[id];
  else {
    userBalances[id] = 0;
    return userBalances[id];
  }
}


/**FAIL - ok*/
int foo21(address id)
   requires   [ub] userBalances::Map<ub>
   ensures   (exists ub0: userBalances'::Map<ub0> & res>0 & res = ub0[id]);
{
  if (userBalances[id] > 0 ) return userBalances[id];
  else {
    userBalances[id] = 0;
    return userBalances[id];
  }
}


/**SUCCESS - should be ok*/
int foo22(address id)
   requires   [ub] userBalances::Map<ub> & ub[id] = value
   ensures   (exists ub0: userBalances'::Map<ub0> & ub0[id] = value + yyy);
{
    int x;
    x = userBalances[id];
    userBalances[id] = x + yyy;
    return userBalances[id];
}

global int org;

/**SUCCESS - should be ok*/
int foo23(address id)
   requires   [ub] userBalances::Map<ub> & ub[id] = org
   ensures   (exists ub0: userBalances'::Map<ub0> & ub0[id] = org + yyy);
{
    int x;
    x = userBalances[id];
    userBalances[id] = x + yyy;
    return userBalances[id];
}

/** SUCCESS - should be ok*/
int foo24(int amount)
   requires mp::Map<mp9> & mp9[0]=org
   ensures  (exists mp1: mp'::Map<mp1> & mp1[0]=org+amount);
{
  mp[0] = mp[0] + amount;
  return mp[0];
}

/**SUCCESS - not ok*/
int foo25(address id)
   requires   [ub] userBalances::Map<ub>
   ensures   (exists ub0: userBalances'::Map<ub0> & ub0[id] = ub[id] + yyy);
{
    int x;
    x = userBalances[id];
    userBalances[id] = x + yyy;
    return userBalances[id];
}

/** SUCCESS - not ok*/
int foo26(int amount)
   requires mp::Map<mp9> & mp9[0]=org
   ensures  (exists mp1: mp'::Map<mp1> & mp1[0]=mp9[0]+amount);
{
  mp[0] = mp[0] + 1;
  mp[0] = mp[0] - 1;
  mp[0] = mp[0] + 1;
  mp[0] = mp[0] - 1;
  mp[0] = mp[0] + amount;
  return mp[0];
}
