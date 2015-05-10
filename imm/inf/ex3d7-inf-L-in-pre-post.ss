data cell{
 int fst;
}

relation P1(ann v1).
  relation P2(ann v1, ann v2,int v,int r).

int foo(cell c)
/*
  requires c::cell<v>@L
  ensures res=v;
*/
  infer [P1,P2]
  requires c::cell<v>@a & P1(a)
  ensures c::cell<v>@b & P2(a,b,v,res)  ;

{
 int x = c.fst;
 return x;
}
/*
# ex3d7.ss --reverify

  infer [P1,P2]
  requires c::cell<v>@a & P1(a)
     ensures  c::cell<v>@b & P2(a,b,v,res)  ;

The above failed, as follows:

Post condition cannot be derived:
  (must) cause:  @L=@L & @L<:b_1458 & @L=b_1458 |-  b_1458=@A. LOCS:[1;0] (must-bug)

despite inferring:

  requires c::cell<v>@a & a=@L
  ensures c::cell<v>@b & res=v & a=@A  ;

We need below, as highlighted in:

  requires c::cell<v>@L
  ensures c::cell<v>@A & res=v  ;


==================================

[RELASS [P1]: ( P1(a)) -->  a<:@L,
RELDEFN P2: ( res=v & b_1458=a & a<:@L & P1(a)) -->  P2(a,b_1458,v,res)]

I think it is sufficient to leave it as:
!!! **pi.ml#658:PRE :  a<:@L

But to later transform pre/post from:

 EBase exists (Expl)[](Impl)[a; v](ex)[]c::cell<v>@a&a<:@L & 
       MayLoop[]&{FLOW,(4,5)=__norm#E}[]
         EAssume 
           (exists v_1457,b_1458: c::cell<v_1457>@b_1458&v_1457=v & res=v & 
           b_1458=a & a<:@L&{FLOW,(4,5)=__norm#E}[]

To:

 EBase exists (Expl)[](Impl)[a; v](ex)[]c::cell<v>@L & 
       MayLoop[]&{FLOW,(4,5)=__norm#E}[]
         EAssume 
           (exists v_1457,b_1458: res=v &{FLOW,(4,5)=__norm#E}[]


!!! **pi.ml#611: P2(a,b_1458,v,res) = ( res=v & b_1458=a & a<:@L)Pi.infer_pure

!!! **fixcalc.ml#1392:n_base:2
!!! **pi.ml#625:bottom_up_fp:[( P2(a,v,b_1458,res), res=v & b_1458=a & a<:@L)]
!!! **pi.ml#632:fixpoint:[( P2(a,v,b_1458,res), res=v & b_1458=a & a<:@L, P1(a), a<:@L)]
!!! **pi.ml#655:REL POST :  P2(a,v,b_1458,res)
!!! **pi.ml#656:POST:  res=v & b_1458=a & a<:@L
!!! **pi.ml#657:REL PRE :  P1(a)
!!! **pi.ml#658:PRE :  a=@L


*/
