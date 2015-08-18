data cell{
 int fst;
}

relation P1(ann v1).
relation P2(ann v1, ann v2).
//relation P3(ann v1, int v,int r, int s).

int foo(cell c)
  infer [P1,P2]
  requires c::cell<v>@a & P1(a)
     /* ensures c::cell<w>@b & P3(b,v,res,w)  ; */
     ensures c::cell<w>@b & P2(a,b) & res=v & (v<=0 & w=v| v>0 & w=5)  ;
{
 int x = c.fst;
 if (x>0) c.fst = 5;
 return x;
}

int foo2(cell c)
  infer [P1,P2]
  requires c::cell<v>@M
     /* ensures c::cell<w>@b & P3(b,v,res,w)  ; */
     ensures c::cell<w>@M & res=v & (v<=0 & w=v| v>0 & w=5)  ;
{
 int x = c.fst;
 if (x>0) c.fst = 5;
 return x;
}

/*
# ex8d2.ss


GOT
---
!!! **pi.ml#770:>>POST:  
((a=@M & res=w_1457 & v=w_1457 & w_1457<=0 & b_1456=@M) 
| (w_1457=5 & a=@M & v=res & b_1456=@M & 1<=res))

Can normalize to:
-----------------
!!! **pi.ml#770:>>POST:  
a=@M & b_1456=@M & ( res=w_1457 & v=w_1457 & w_1457<=0 ) 
                    | (w_1457=5 & v=res & 1<=res)


!!! **pi.ml#696:reloblgs:[( P1(a,v), (a=@M | (v<=0 & a<:@L)))]

Maybe can strengthen this to:

!!! **pi.ml#696:reloblgs:[( P1(a,v), (a=@M | a<:@L))]
!!! **pi.ml#696:reloblgs:[( P1(a,v), a=@M] [DONE]


if SAT(a=@M & (v<=0 & a<:@L)) then strengthen  (a=@M | (v<=0 & a<:@L))
strengthen  (a=@M | (v<=0 & a<:@L)) = 
 = strengthen (imm(a=@M | (v<=0 & a<:@L)) & strengthen (pure(a=@M | (v<=0 & a<:@L))
 = strengthen (a=@M | a<:@L) & strengthen (true | v<=0)
 = a=@M & true



*/
