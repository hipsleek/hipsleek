hip_include 'scontracts/mapprimitives.ss'

global mapping(int => int) mp;

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

int call_foo1()
   requires  mp::Map<mp8>
   ensures   (exists mp9: mp::Map<mp9> & res=14);
{
 int x = foo1();
 return x;
}


M: lvref*->gvref*
forall proc(vref*,v*) with pre/post \in P .
    fresh v_*,vref_*,
    \rho1=[v_*/v*] and
    \rho2=[M[vref*]/vref* | M[vref*]!=\bot] \union [vref_*/vref* | M[vref*]=\bot]
    \rho = \rho1 \union \rho2
    UNSAT(forall v_*. \rho(pre) /\ \delta_pre)
---------------------------------------------------------------------------
                 {\delta_pre} call(w*) {\delta_post}
---needs to create contradiction with all the methods that alter the state
