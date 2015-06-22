//hip_include '../prelude_aux.ss'
//#option --ato
relation P(int a,int r).

int foo(int[] a)
 //infer [@arrvar] requires true ensures res=a[5];
//infer [@arrvar,P] requires true ensures P(res,a[5]);
  infer [@arrvar,P] requires true ensures P(res,a[4]);
{
  return a[5];
}

/*

infer [@arrvar,P] requires true ensures P(res,a[4]);

Post Inference result:
foo$int[]
 EBase htrue&exists(res:exists(a:a[5]=res)) & MayLoop[]&
       {FLOW,(4,5)=__norm#E}[]
         EAssume 
           emp&a[5]=res&{FLOW,(4,5)=__norm#E}[]

!!! **pi.ml#610: P(res,a[4]) = ( a[5]=res)Pi.infer_pure
!!! **fixcalc.ml#1396:n_base:2Omega Error Exp:Globals.Illegal_Prover_Format("Omega.omega_of_exp: array, bag or list constraint  a[5]")
 Formula: a[5]=res

!!! bottom_up_fp0:[( P(a[4],res), a[5]=res)]
!!! **pi.ml#624:bottom_up_fp:[( P(a[4],res), a[5]=res)]
!!! pre_rel_fmls:[]
!!! pre_fmls:[ true, MayLoop[]]
!!! pre_invs:[ true]
!!! **pi.ml#632:fixpoint:[( P(a[4],res), a[5]=res, true, true)]
!!! **pi.ml#646:1>REL POST :  P(a[4],res)
!!! **pi.ml#647:1>POST:  a[5]=res
!!! **pi.ml#648:1>REL PRE :  true
!!! **pi.ml#649:1>PRE :  trueOmega Error Exp:Globals.Illegal_Prover_Format("Omega.omega_of_exp: array, bag or list constraint  a[5]")
 Formula: exists(res:exists(a:a[5]=res))

!!! **pi.ml#662:REL POST :  P(a[4],res)
!!! **pi.ml#663:POST:  a[5]=res
!!! **pi.ml#664:REL PRE :  true
!!! **pi.ml#665:PRE :  exists(res:exists(a:a[5]=res))Omega Error Exp:Globals.Illegal_Prover_Format("Omega.omega_of_exp: array, bag or list constraint  a[5]")
 Formula: exists(res:exists(a:a[5]=res))

*/
