relation Q(int n,int r).

int foo(int n)
  infer [Q]
  requires true  ensures Q(n,res);
{
  return 1+n;
}



/*
# sim2-pre.ss 

Correct result, but we can remove some unnecessary printing

>>>>>>>>>>>>>> NOT NEEDED
!!! proc_specs:[ EInfer [Q]
   EBase htrue&{FLOW,(4,5)=__norm#E}[]
           EBase emp&MayLoop[]&{FLOW,(4,5)=__norm#E}[]
                   EAssume 
                     emp&Q(n,res)&{FLOW,(4,5)=__norm#E}[]
                     ]
<<<<<<<<<<<<<<<<<<<<<<<<<

*************************************
******pure relation assumption*******
*************************************
[RELDEFN Q: ( n+1=res) -->  Q(n,res)]
*************************************

>>>>>>>>>>>>>> NOT NEEDED
!!! constraints:[( n+1=res, Q(n,res))]
!!! bottom_up_fp:[( Q(n,res), n=res-1)]
!!! fixpoint:[( Q(n,res), n=res-1, true, true)]
*************************************
*******fixcalc of pure relation *******
*************************************
[( Q(n,res), n=res-1, true, true)]
*************************************
<<<<<<<<<<<<<<<<<<<<<<<<<
>>>>>>> KEEP BELOW (what is fixpoint?)
!!! bottom_up_fp:[( Q(n,res), n=res-1)]
!!! fixpoint:[( Q(n,res), n=res-1, true, true)]
<<<<<<<<<<<<<<<<<<<<<<<<<

!!! REL POST :  Q(n,res)
!!! POST:  n=res-1
!!! REL PRE :  true
!!! PRE :  true
Post Inference result:
foo$int
 EBase htrue&MayLoop[]&{FLOW,(4,5)=__norm#E}[]
         EAssume 
           emp&n=res-1&{FLOW,(4,5)=__norm#E}[]


*/
