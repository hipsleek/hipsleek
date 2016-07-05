data cell{
 int fst;
}

relation P(ann v1).
//relation P3(ann v1, int v,int r, int s).

int foo(cell c)
  infer [P]
  requires c::cell<v>@a & P(a)
     /* ensures c::cell<w>@b & P3(b,v,res,w)  ; */
     ensures c::cell<w>@b   ;
{
 int x = c.fst;
 if (x>0) c.fst = 5;
 return x;
}


int foo2(cell c)
  infer [P]
  requires c::cell<v>@a & a=@M
/* ensures c::cell<w>@b & P3(b,v,res,w)  ; */
  ensures c::cell<w>@b & P(b)   ;
{
  int x = c.fst;
  if (x>0) c.fst = 5;
  return x;
}

/*
# ex8d3.ss

GOT
---
!!! **pi.ml#678:reldefns:[( a=@M, P1(a))]
!!! **pi.ml#679:reldefns_from_oblgs:[( a=@M, P1(a))]

Post Inference result:
foo$cell
 EBase exists (Expl)[](Impl)[a; v](ex)[]c::cell<v>@a&a=@M & MayLoop[]&
       {FLOW,(4,5)=__norm#E}[]
         EAssume 
           (exists b_1449,w_1450: c::cell<w_1450>@b_1449&
           {FLOW,(4,5)=__norm#E}[]



*/
