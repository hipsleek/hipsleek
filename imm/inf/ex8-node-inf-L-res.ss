data cell{
 int fst;
}

relation P1(ann v1).
relation P2(ann v1, ann v2,int v,int r, int s).
relation P3(ann v1, int v,int r, int s).

int foo(cell c)
  infer [P1,P2]
  requires c::cell<v>@a & P1(a)
     /* ensures c::cell<w>@b & P3(b,v,res,w)  ; */
     ensures c::cell<w>@b & P2(a,b,v,res,w)  ;
{
 int x = c.fst;
 c.fst = 5;
 return x;
}

/*
../../hip ex8-node-inf-L-res.ss 

[RELASS [P1]: ( P1(a)) -->  a<:@L,
RELASS [P1]: ( P1(a)) -->  (a=@M | a=@A),
RELDEFN P2: ( v=res & w_1456=5 & a<:@L & @M<:b_1455 & P1(a)) -->  P2(a,b_1455,v,res,w_1456)]
*************************************

!!! **pi.ml#634:pre_rel_ids:[P1]
!!! **pi.ml#635:post_rel_ids:[P2]
!!! **pi.ml#636:pre_ref_df:[]
!!! **pi.ml#637:post_ref_df:[( v=res & w_1456=5 & a<:@L & @M<:b_1455 & P1(a), P2(a,b_1455,v,res,w_1456))]
!!! **pi.ml#638:WN: why is pre_rel_df empty? It should be P1(a) = a=@M

~~~~ before enabling the instantiating of v=@A

this was ok initially:

!!! **pi.ml#712:new_specs2:[ EInfer [P1,P2]
   EBase exists (Expl)[](Impl)[a; v](ex)[]c::cell<v>@a&a=@M&
         {FLOW,(4,5)=__norm#E}[]
           EBase emp&a=In_1 & MayLoop[]&{FLOW,(4,5)=__norm#E}[]
                   EAssume 
                     (exists b_1451,w_1452: c::cell<w_1452>@b_1451&v=res & 
                     b_1451=@M & w_1452=5 & a<:@L&{FLOW,(4,5)=__norm#E}[]
                     ]

but after normalization a=@L which is too strong:
Post Inference result:
foo$cell
 EBase exists (Expl)[](Impl)[a; v](ex)[]c::cell<v>@a&a=@M & a=In_1 & 
       MayLoop[]&{FLOW,(4,5)=__norm#E}[]
         EAssume 
           (exists b_1451,w_1452: c::cell<w_1452>@b_1451&v=res & b_1451=@M & 
           w_1452=5 & a=@L&{FLOW,(4,5)=__norm#E}[]


===========================================
~~~~ after enabling the instantiating of v=@A

!!! **pi.ml#712:new_specs2:[ EInfer [P1,P2]
   EBase exists (Expl)[](Impl)[a; v](ex)[]c::cell<v>@a&a=@M&
         {FLOW,(4,5)=__norm#E}[]
           EBase emp&a=In_1 & MayLoop[]&{FLOW,(4,5)=__norm#E}[]
                   EAssume 
                     (exists b_1455,w_1456: c::cell<w_1456>@b_1455&v=res & 
                     b_1455=@A & w_1456=5 & a<:@L&{FLOW,(4,5)=__norm#E}[]
                     ]
Post Inference result:
foo$cell
 EBase exists (Expl)[](Impl)[a; v](ex)[]c::cell<v>@a&a=@M & a=In_1 & 
       MayLoop[]&{FLOW,(4,5)=__norm#E}[]
         EAssume 
           (exists b_1455,w_1456: c::cell<w_1456>@b_1455&v=res & b_1455=@A & 
           w_1456=5 & a=@L&{FLOW,(4,5)=__norm#E}[]


*/
