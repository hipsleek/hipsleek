data cell{
 int fst;
}

relation P1(ann v1).
relation P2(ann v1).

void foo(cell c)
  infer [P1,P2]
  requires c::cell<v>@a & P1(a)
  ensures c::cell<2>@b & P2(b)  ;
{
  c.fst = 2;
}
/*
# cell-3b.ss

[RELASS [P1]: ( P1(a)) -->  a=@M,
RELDEFN P2: ( b=@M) -->  P2(b)]

 c::cell<v>@a & P1(a) |- c::cell<_>

     P1(a) --> a<:M

 c::cell<v>@a & a<:M |- c::cell<_>@b & P2(b)

     b<:@M -> P2(b)

*************************************
Two problems:
 (1) why numeric for fixcalc?
 (2) Why false for PRE?

*************************************
*******fixcalc of pure relation *******
*************************************
[( P2(b), b=0, P1(a), false)]
*************************************

!!!REL POST :  P2(b)
!!!POST:  b=0
!!!REL PRE :  P1(a)
!!!PRE :  false

*************************************
*******fixcalc of pure relation *******
*************************************
[( P2(b), b=0, P1(a), false)]

*/
