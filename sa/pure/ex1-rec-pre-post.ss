

relation P(int a).
relation Q(int a, int b).

int foo(int x)
  infer [P,Q] requires P(x) ensures Q(x,res);
{
  if (x<10){
    x=x+1;
    return foo(x);
  }

  return x;
}


/*
*************************************
******pure relation assumption*******
*************************************
[RELDEFN P: ( x=x'-1 & x'<=10 & P(x)) -->  P(x'),
RELDEFN Q: ( x'=x+1 & x<=9 & Q(x',res) & P(x)) -->  Q(x,res),
RELDEFN Q: ( x=res & 10<=res & P(x)) -->  Q(x,res)]
*************************************

!!! **pi.ml#610: Q(x,res) = ( x=res & 10<=res) \/ ( x'=x+1 & x<=9 & Q(x',res))Pi.infer_pure

!!! **fixcalc.ml#1386:n_base:2### args:[ x, res]
compute_def vars: [[x:int,res:int]]
### compute_fixpoint_aux def:Q:={[x] -> [res] -> []: (x=res && 10<=res ||  (exists (PRIx:PRIx=x+1 && Q(PRIx,res)))  && x<=9)
};

!!! **fixcalc.ml#888:bottom up
!!! **pi.ml#624:bottom_up_fp:[( Q(x,res), ((9>=x & 10=res) | (res>=10 & res=x)))]
!!! **pi.ml#631:fixpoint:[( Q(x,res), ((9>=x & 10=res) | (res>=10 & res=x)), P(x), true)]
!!! **pi.ml#652:REL POST :  Q(x,res)
!!! **pi.ml#653:POST:  ((9>=x & 10=res) | (res>=10 & res=x))
!!! **pi.ml#654:REL PRE :  P(x)
!!! **pi.ml#655:PRE :  true


 */
