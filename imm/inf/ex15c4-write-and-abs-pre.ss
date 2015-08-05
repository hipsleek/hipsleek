
data cell{
 int fst;
}

relation P(ann v,ann w).

int foo2(cell c, cell d)
//  infer [@imm_pre,@pre_n]
  infer [@imm_pre]
  requires c::cell<_> * d::cell<_>
  ensures c::cell<_> * d::cell<_>;
/*
   infer [P] 
   requires c::cell<_>@a1 * d::cell<_>@a2 & P(a1,a2) 
   ensures c::cell<_>@a3 * d::cell<_>@a4; */
{
  int x = c.fst;
  if (x>0) c.fst = 5;
  return x;
}

/*
# ex15c1.ss

infer [P]
  requires c::cell<_>@a1 * d::cell<_>@a2 & P(a1,a2)
  ensures c::cell<_> * d::cell<_>;

# Why isn't a2=@A since d is not accessed?

 EInfer []
   EBase 
     exists (Expl)[](Impl)[a1; Anon_11; a2; 
     Anon_12](ex)[]c::cell<Anon_11>@a1 * d::cell<Anon_12>@a2&a2=@M & a1=@M & 
     MayLoop[]&{FLOW,(4,5)=__norm#E}[]
     EAssume 
       (exists Anon_1210,Anon_1211: c::cell<Anon_1210>@M * 
       d::cell<Anon_1211>@M&{FLOW,(4,5)=__norm#E}[]Stop Omega... 321 invocations

------------------------------------------------
i) TO FIX the imm_unify

!!! **immutable.ml#62:imm + pure:[( ann_1227=@M, true),( ann_1227<:@L, Anon_11<=0),( ann_1227=@A, true)]
(====)
split_imm_pure@18@17@16
split_imm_pure inp1 : (ann_1227=@M | (ann_1227<:@L & Anon_11<=0) | ann_1227=@A)
split_imm_pure@18 EXIT:( ann_1227=@M & ann_1227<:@L & ann_1227=@A, true)

(====)
imm_unify@17@16
imm_unify inp1 : (ann_1227=@M | (ann_1227<:@L & Anon_11<=0) | ann_1227=@A)
imm_unify@17 EXIT: ann_1227=@M & ann_1227<:@L & ann_1227=@A


------------------------------------------------
ii) we still need to make imm_pre & imm_post independent of post_n & pre_n

*************************************
******pure relation assumption 1 *******
*************************************
[RELASS [P__1229]: ( P__1229(ann_1228,ann_1227)) -->  ann_1228<:@A & ann_1227<:@A,
RELASS [P__1229]: ( P__1229(ann_1228,ann_1227)) -->  ann_1227<:@L,
RELASS [pre_1232,P__1229]: ( pre_1232(Anon_11,Anon_12) & P__1229(ann_1228,ann_1227)) -->  (ann_1227=@M | (ann_1227<:@L & Anon_11<=0) | ann_1227=@A)]
*************************************


iii)

=======================================================
# ex15c4.ss
TO FIX the imm_unify

!!! **immutable.ml#62:imm + pure:[( ann_1227=@M, true),( ann_1227<:@L, Anon_11<=0),( ann_1227=@A, true)]
(====)
split_imm_pure@18@17@16
split_imm_pure inp1 : (ann_1227=@M | (ann_1227<:@L & Anon_11<=0) | ann_1227=@A)
split_imm_pure@18 EXIT:( ann_1227=@M & ann_1227<:@L & ann_1227=@A, true)

(====)
imm_unify@17@16
imm_unify inp1 : (ann_1227=@M | (ann_1227<:@L & Anon_11<=0) | ann_1227=@A)
imm_unify@17 EXIT: ann_1227=@M & ann_1227<:@L & ann_1227=@A

=======================================================
# ex15c4.ss to add ann_1226, ann_1225 to the list of existential vars (FIXED)

!!! **pi.ml#384:new_spec:
 EInfer @imm_pre[P__1229]
   EBase 
     exists (Expl)[](Impl)[Anon_11; 
     Anon_12](ex)[]c::cell<Anon_11>@ann_1227 * d::cell<Anon_12>@ann_1228&
     P__1229(ann_1228,ann_1227)&{FLOW,(4,5)=__norm#E}[]
     EBase 
       emp&MayLoop[]&{FLOW,(4,5)=__norm#E}[]
       EAssume 
         (exists Anon_1207,Anon_1208: c::cell<Anon_1207>@ann_1225 * 
         d::cell<Anon_1208>@ann_1226&{FLOW,(4,5)=__norm#E}[]
*/
