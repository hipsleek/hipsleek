data cell{
 int fst;
}

relation P1(ann v1).
relation P2(ann v1, ann v2,int v,int r, int s).

int foo(cell c)
  infer [P1,P2]
  requires c::cell<v>@a & P1(a)
  ensures c::cell<w>@b & P2(a,b,v,res,w)  ;
{
 int x = c.fst;
 return x;
}
/********************
# ex8b2.ss

We obtained:

[RELASS [P1]: ( P1(a)) -->  a<:@L,
RELDEFN P2: ( w_1450=res & v=res & a<:@L & a<:b_1449 & P1(a)) -->  P2(a,b_1449,v,res,w_1450)]

..


inferred pre:    c::cell<v>@a&a<:@L 
inferred post   (exists b_1464,w_1465: c::cell<w_1465>@b_1464&w_1465=res & v=res & a<:@L & a<:b_1464)
*********************/


