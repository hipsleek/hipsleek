//hip_include '../prelude_aux.ss'
//#option --ato
relation P(int a).
relation Q(int a,int r).

int foo(int[] a)
 //infer [@arrvar] requires true ensures res=a[5];
  infer [@arrvar,P,Q] requires P(a[5]) ensures Q(res,a[5]);
//  infer [@arrvar,P] requires true ensures P(res,a[4]);
{
  if (a[5]>10) {
    return a[5];
  } else {
    assume false;
    return -1;
  }
}

/*
# ex11a2.ss --ato

[RELDEFN Q: ( a[5]=res & 11<=res & P(a[5])) -->  Q(res,a[5])]

*************************************

!!! **pi.ml#610: Q(res,a[5]) = ( a[5]=res & 11<=res)
!!! **pi.ml#614:bottom_up_fp0:[( Q(a[5],res), a[5]=res & 11<=res)]
!!! **pi.ml#632:fixpoint:[( Q(a[5],res), a[5]=res & 11<=res, P(a[5]), 11<=(a[5]))]
!!! **pi.ml#646:>>REL POST :  Q(a[5],res)
!!! **pi.ml#647:>>POST:  a[5]=res & 11<=res
!!! **pi.ml#648:>>REL PRE :  P(a[5])
!!! **pi.ml#649:>>PRE :  11<=(a[5])
Post Inference result:
foo$int[]
 EBase emp&11<=(a[5]) & MayLoop[]&{FLOW,(4,5)=__norm#E}[]
         EAssume 
           emp&a[5]=res & 11<=res&{FLOW,(4,5)=__norm#E}[]
# without --ato (Omega error detected)

!!! **pi.ml#610: Q(res,a[5]) = ( a[5]=res & 11<=res)Omega Error Exp:Globals.Illegal_Prover_Format("Omega.omega_of_exp: array, bag or list constraint  a[5]")
 Formula: a[5]=res & 11<=res

!!! **pi.ml#614:bottom_up_fp0:[( Q(a[5],res), a[5]=res & 11<=res)]Omega Error Exp:Globals.Illegal_Prover_Format("Omega.omega_of_exp: array, bag or list constraint  a[5]")
 
 */
