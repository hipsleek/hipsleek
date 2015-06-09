//hip_include '../prelude_aux.ss'
//#option --ato
relation P(int[] a).
  relation Q(int[] a,int[] b,int r).

int foo(ref int[] a)
 //infer [@arrvar] requires true ensures res=a[5];
//  infer [@arrvar,P,Q] requires P(a) ensures Q(a,a',res);
  infer [P,Q,update_array_1d] requires P(a) ensures Q(a,a',res);
// requires true ensures update(a,a',10,5) & res=a[4];
// requires true ensures a'[5]=10 & res=a[4];
{
  a[5]=10;
  return a[4];
}

/*
# ex11d5.ss 

  infer [P,Q,update_array_1d] requires P(a) ensures Q(a,a',res);

# without arrvar, more exceptions.

!!! **omega.ml#561:WARNING: exception from Omega.is_sat_ops
!!! **omega.ml#561:WARNING: exception from Omega.is_sat_ops
!!! **omega.ml#673:WARNING: exception from Omega.is_valid
!!! **omega.ml#561:WARNING: exception from Omega.is_sat_ops
!!! **omega.ml#561:WARNING: exception from Omega.is_sat_opsOmega Error Exp:Globals.Illegal_Prover_Format("Omega.omega_of_exp: array, bag or list constraint  a'[4]")

!!! **infer.ml#2153:Rel Inferred::[RELDEFN Q: ( exists(v_int_14_1405':res=v_int_14_1405' & v_int_14_1405'=a'[4]) & 
update_array_1d(a,a',10,5) & P(a)) -->  Q(a,a',res)]


*/
