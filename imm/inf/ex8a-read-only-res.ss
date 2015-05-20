data cell{
 int fst;
}

relation P1(ann v1).
relation P2(ann v1, ann v2,int v,int r, int s).
relation P3(ann v1, int v,int r, int s).

int foo(cell c)
  infer [P1,P2]
  requires c::cell<vvv>@aaa & P1(aaa)
     /* ensures c::cell<w>@b & P3(b,v,res,w)  ; */
     ensures c::cell<w>@bbb & P2(aaa,bbb,vvv,res,w)  ;
{
 int x = c.fst;
 dprint;
 //c.fst = 5;
 return x;
}

/*
../../hip ex8a.ss --reverify

[RELASS [P1]: ( P1(a)) -->  a<:@L,
RELDEFN P2: ( w_1454=res & v=res & a<:@L & a<=b & P1(a)) 
    -->  P2(a,b,v,res,w_1454)]

#  Expecting a<:b



*/
