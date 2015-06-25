data cell{
 int fst;
}

relation P(ann v).

  int foo2(int x,cell c)
  infer [P]
  requires c::cell<v>@a & a=@L
     /* ensures c::cell<w>@b & P3(b,v,res,w)  ; */
     ensures c::cell<w>@b & P(b);
{
 if (x>0) return c.fst;
 return x;
}

/*
# ex8d7.ss

  requires c::cell<v>@a & a=@L
     /* ensures c::cell<w>@b & P3(b,v,res,w)  ; */
     ensures c::cell<w>@b & P(b);
{
 if (x>0) return c.fst;
 return x;
}

# Got P(x) = x=@A
# However, expects P(x) = x=@L;
  as we expect post to be strengthened.

*************************************
******pure relation assumption 1 *******
*************************************
[RELDEFN P: ( @L<:b_1468) -->  P(b_1468)]
*************************************

!!! **pi.ml#754:fixpoint:[( P(b_1468), @L<:b_1468, true, true)]
!!! **pi.ml#775:>>REL POST :  P(b_1468)
!!! **pi.ml#776:>>POST:  b_1468=@A

   EBase exists (Expl)[](Impl)[a; v](ex)[]c::cell<v>@a&a=@L&
         {FLOW,(4,5)=__norm#E}[]
           EBase emp&MayLoop[]&{FLOW,(4,5)=__norm#E}[]
                   EAssume 
                     (exists w_1467,b_1468: c::cell<w_1467>@b_1468&b_1468=@A&
                     {FLOW,(4,5)=__norm#E}[]
                     ]

*/
