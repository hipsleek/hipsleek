hip_include 'scontracts/mapprimitives.ss'

global mapping(int => int) mp;

global int x;

int goo()
    requires x>0
    ensures  x'=0;
{
 x = 0;
 return 0;
}


/** why goo works fine while for foo HIP complains about not finding mp? */
/** !! see the error below !! */

int foo()
   requires mp::Map<mp9>@L
   ensures  res=9;
{
  mp[0] = 9; // => update(mp,0,9)[int,int];
  int x = mp[0];
  dprint;
  return x;
}


/**

Last Proving Location: test-map-21-bug.ss_15:0_0:-1

ERROR: at test-map-21-bug.ss_19:2_19:4
Message: Var mp is not defined
Exception(helper_trans_exp):Failure("Var mp is not defined")
Exception(helper_trans_exp):Failure("Var mp is not defined")
Exception(trans_exp):Failure("Var mp is not defined")
Exception(helper_trans_exp):Failure("Var mp is not defined")
Exception(trans_exp):Failure("Var mp is not defined")
Exception(helper_trans_exp):Failure("Var mp is not defined")
Exception(trans_exp):Failure("Var mp is not defined")
Exception(helper_trans_exp):Failure("Var mp is not defined")
Exception(helper_trans_exp):Failure("Var mp is not defined")
Exception(trans_exp):Failure("Var mp is not defined")
Exception(trans_proc):Failure("Var mp is not defined")
Exception(trans_prog):Failure("Var mp is not defined")
Stop z3... 48 invocations
Stop Omega... 14 invocations caught

Exception occurred: Failure("Var mp is not defined")
Error3(s) detected at main

*/
