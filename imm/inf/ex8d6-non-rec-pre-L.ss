data cell{
 int fst;
}

relation P(ann v).

  int foo2(int x,cell c)
  infer [P]
  requires c::cell<v>@a & P(a)
     /* ensures c::cell<w>@b & P3(b,v,res,w)  ; */
  ensures c::cell<w>@b ;
{
 if (x>0) return c.fst;
 return x;
}

/*
# ex8d6.ss

*************************************
******pure relation assumption 1 *******
*************************************
[RELASS [P]: ( P(a)) -->  a<:@L]
*************************************

!!! **pi.ml#677:post_rel_ids:[]
!!! **pi.ml#678:reldefns:[( a<:@L, P(a))]
!!! **pi.ml#679:reldefns_from_oblgs:[( a<:@L, P(a))]
!!! **pi.ml#680:initial reloblgs:[( P(a), a<:@L)]
!!! **pi.ml#681:reloblgs:[( P(a), a<:@L)]
!!! **pi.ml#682:lst_assume:[( P(a), a<:@L)]
!!! **pi.ml#683:pre_rel_fmls:[ P(a)]
!!! **pi.ml#684:pre_ref_df:[( a<:@L, P(a))]

Can we strengthen this pre to

  P(x) == x=@L


*/
