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

# using b=@A is too weak..

[RELDEFN P: ( b_1452=@A) -->  P(b_1452)]

GOT
---
!!! **pi.ml#802:new_specs2:[ EInfer [P]
   EBase exists (Expl)[](Impl)[a; v](ex)[]c::cell<v>@a&a=@M&
         {FLOW,(4,5)=__norm#E}[]
           EBase emp&MayLoop[]&{FLOW,(4,5)=__norm#E}[]
                   EAssume 
                     (exists w_1451,b_1452: c::cell<w_1451>@b_1452&b_1452=@A&
                     {FLOW,(4,5)=__norm#E}[]
                     ]




*/
