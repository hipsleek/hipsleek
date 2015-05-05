//hip_include '../prelude_aux.ss'
//#option --ato
relation P(int[] a).
relation Q(int[] a,int r).

int foo(int[] a)
 //infer [@arrvar] requires true ensures res=a[5];
  infer [@arrvar,P,Q] requires P(a) ensures Q(a,res);
// requires a[5]>0 ensures res=a[5];
{
  if (a[5]>10) {
    return a[5];
  } else {
    assume false;
    return -1;
  }
}

/*
# ex11c.ss --ato

*************************************
******pure relation assumption*******
*************************************
[RELDEFN Q: ( a[5]=res & 11<=res & P(a)) -->  Q(a,res)]
*************************************

!!! **pi.ml#613: Q(a,res) = ( a[5]=res & 11<=res)
!!! **pi.ml#616:sp:compute_fixpoint: EInfer @arrvar[P,Q]
   EBase emp&P(a)&{FLOW,(4,5)=__norm#E}[]
           EBase emp&MayLoop[]&{FLOW,(4,5)=__norm#E}[]
                   EAssume 
                     emp&Q(a,res)&{FLOW,(4,5)=__norm#E}[]
                     
!!! **pi.ml#619:bottom_up_fp0:[( Q(a,res), a[5]=res & 11<=res)]
!!! **pi.ml#636:fixpoint:[( Q(a,res), a[5]=res & 11<=res, P(a), 11<=(a[5]))]
!!! **pi.ml#650:>>REL POST :  Q(a,res)
!!! **pi.ml#651:>>POST:  a[5]=res & 11<=res
!!! **pi.ml#652:>>REL PRE :  P(a)
!!! **pi.ml#653:>>PRE :  11<=(a[5])
Post Inference result:
foo$int[]
 EBase emp&11<=(a[5]) & MayLoop[]&{FLOW,(4,5)=__norm#E}[]
         EAssume 
           emp&a[5]=res & 11<=res&{FLOW,(4,5)=__norm#E}[]

*/
