data cell{
 int fst;
}

relation P(ann v).

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
# ex8d4.ss

!!! **pi.ml#743:pre_fmls:[ a=@M & c=2, MayLoop[]]
!!! **pi.ml#748:fixpoint:[( P(b_1452), @M<:b_1452, true, true)]
!!! **pi.ml#769:>>REL POST :  P(b_1452)
!!! **pi.ml#770:>>POST:  b_1452=@M

# How is post strengthened? Is it safe?

It seems safe only after pre-condition has been strengthened.
Also, it seems safe cos we are merely strenthening the
earlier instantiation.

*/
