hip_include 'scontracts/mapprimitives.ss'

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
