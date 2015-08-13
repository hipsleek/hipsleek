relation R(int x,int a).
relation R2(int x,int a).

void loo (ref int x, int a)
  infer [R,R2]
     requires R(x,a)
     ensures true;
{

  if (x>0) {
    a=a+1;
    x = x+a-1;
    loo2(x,a);
  };
}

void loo2 (ref int xx, int aa)
  infer [R,R2]
     requires R2(xx,aa)
     ensures true;
{

  if (xx>0 ) {
    aa=aa+1;
    xx = xx+aa-1;
    loo(xx,aa);
  };
}

/*
# ex26c.ss

# Why warning here.

!!! **typechecker.ml#836:WARNING : Spurious RelInferred (not collected):[RELDEFN R2: ( a'=a+1 & x=x'-a & a<x' & R(x,a)) -->  R2(x',a')]

!!! **infer.ml#2213:RelInferred (simplified):
  [RELDEFN R2: ( a'=a+1 & x=x'-a & a<x' & R(x,a)) -->  R2(x',a')]

loo -> loo2
!!! analyse_param summary:
!!! relations (normalised):[( a'=a+1 & x=x'-a & a<x' & R(x,a), R2(x',a'))]
!!! args:[(int,x),(int,a)]
!!! result:[[IND([a,x], (1*a)+(1*x)),IND([a], (1*a)+1)]]

!!! **infer.ml#2213:RelInferred (simplified):
[RELDEFN R: ( aa'=aa+1 & xx=xx'-aa & aa<xx' & R2(xx,aa)) -->  R(xx',aa')]

loo2:
!!! analyse_param summary:
!!! relations (normalised):[( aa'=aa+1 & xx=xx'-aa & aa<xx' & R2(xx,aa), R(xx',aa'))]
!!! args:[(int,xx),(int,aa)]
!!! result:[[IND([aa,xx], (1*aa)+(1*xx)),IND([aa], (1*aa)+1)]]


 */
