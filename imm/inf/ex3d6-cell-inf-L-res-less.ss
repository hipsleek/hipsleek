data cell{
 int fst;
}

relation P1(ann v1).
relation P2(ann v2,int v,int r).

int foo(cell c)
/*
  requires c::cell<v>@L
  ensures res=v;
*/
  infer [P1,P2]
  requires c::cell<v>@a & P1(a)
  ensures c::cell<v>@b & P2(b,v,res)  ;

{
 int x = c.fst;
 return x;
}
/*
# ex3d6.ss

  infer [P1,P2]
  requires c::cell<v>@a & P1(a)
  ensures c::cell<v>@b & P2(a,b,res)  ;

[RELASS [P1]: ( P1(a)) -->  a<:@L,
RELDEFN P2: ( P1(b_1457) & b_1457<:@L & res=v) -->  P2(b_1457,v,res)]

Below isn't correct.Expects:
   P1(a) == a<:@L
which can be used to later strengthen pre-cond to x::Cell<..>::@L

!!! **pi.ml#611: P2(b_1457,v,res) = ( b_1457<:@L & res=v)Pi.infer_pure

!!! **fixcalc.ml#1392:n_base:2
!!! **pi.ml#625:bottom_up_fp:[( P2(v,b_1457,res), b_1457<:@L & res=v)]
!!! **pi.ml#632:fixpoint:[( P2(v,b_1457,res), b_1457<:@L & res=v, P1(a), true)]
!!! **pi.ml#655:REL POST :  P2(v,b_1457,res)
!!! **pi.ml#656:POST:  b_1457<:@L & res=v
!!! **pi.ml#657:REL PRE :  P1(a)
!!! **pi.ml#658:PRE :  true

*/
