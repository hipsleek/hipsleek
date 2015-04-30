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
# ex3d5.ss

  infer [P1,P2]
  requires c::cell<v>@a & P1(a)
  ensures c::cell<v>@b & P2(a,b,res)  ;

[RELASS [P1]: ( P1(a)) -->  a<:@L,
RELDEFN P2: ( P1(b_1457) & b_1457<:@L & res=v) -->  P2(b_1457,v,res)]


*/
