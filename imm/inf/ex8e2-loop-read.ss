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
 if (x!=0) {
   return 2+foo(c);
 } else return 0;
}

/*
# ex8e1.ss

How was post_ref_df_new derived from post_ref_df?

!!! **pi.ml#696:reloblgs:[( P1(a,v), (a=@M | (v=0 & a<:@L)))]

!!! **pi.ml#702:post_ref_df:[( 
res=0 & w_1470=0 & v=0 & a<:@L & a<:b_1469 & P1(a,v), 
P2(a,b_1469,v,res,w_1470))]
!!! **pi.ml#717:post_ref_df_new:[( 
res=0 & w_1470=0 & v=0 & a<:@L & a<:b_1469 
& 1<=v & a<:@L & P1(a,v) & v_1517+1=v & @M<:a_1516, 
P2(a,b_1469,v,res,w_1470))]


*/
