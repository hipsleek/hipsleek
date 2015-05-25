data cell{
 int fst;
}

relation P1(ann v1, int v).
relation P2(ann v1, ann v2,int v,int r, int s).
//relation P3(ann v1, int v,int r, int s).

int foo(cell c)
  infer [P1,P2]
  requires c::cell<v>@a & P1(a,v)
     /* ensures c::cell<w>@b & P3(b,v,res,w)  ; */
     ensures c::cell<w>@b & P2(a,b,v,res,w)  ;
{
 int x = c.fst;
 if (x>0) c.fst = 5;
 return x;
}

/*
# ex8d2.ss

!!! **pi.ml#696:reloblgs:[( P1(a,v), (a=@M | (v<=0 & a<:@L)))]

Maybe can strengthen this to:

!!! **pi.ml#696:reloblgs:[( P1(a,v), (a=@M | a<:@L))]
!!! **pi.ml#696:reloblgs:[( P1(a,v), a=@M]


*/
