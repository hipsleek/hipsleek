data cell{
 int fst;
}
/*
relation P1(ann v1).
relation P2(ann v1, ann v2).*/
//relation Q(ann v1).
//relation P3(ann v1, int v,int r, int s).

int foo(cell c)
  infer [@imm_pre]
  requires c::cell<v>
  ensures c::cell<w>  ;
{
 int x = c.fst;
 if (x!=1) {
   //c.fst =c.fst-1;
   dprint;
   int tmp=2+foo(c);
   dprint;
   return tmp;
 } else return 0;
}


/*
>>>>>>>> ex17a1.ss 
Proving precondition in method foo$cell Failed.
  (may) cause:  ann_1221<:@L & P__1222(ann_1221) |-  ann_1221<:ann_1239. LOCS:[1;12;0] (may-bug)

Context of Verification Failure: _0:0_0:0

Last Proving Location: ex17a1-heavy.ss_19:13_19:19

Procedure foo$cell FAIL.(2)

....

!!! **pi.ml#384:new_spec:
 EInfer @imm_pre[P__1222]
   EBase 
     exists (Expl)[](Impl)[v](ex)[]c::cell<v>@ann_1221&P__1222(ann_1221)&
     {FLOW,(4,5)=__norm#E}[]
     EBase 
       emp&MayLoop[]&{FLOW,(4,5)=__norm#E}[]
       EAssume 
         (exists w_1203,ann_1220: c::cell<w_1203>@ann_1220&
         {FLOW,(4,5)=__norm#E}[]
----------------------------------------------------------------------------------------------------------  

instead of
  EBase 
     exists (Expl)[](Impl)[v](ex)[]c::cell<v>@ann_1221&P__1222(ann_1221)&

we should have:
  EBase 
     exists (Expl)[](Impl)[v, ann_1221](ex)[]c::cell<v>@ann_1221&P__1222(ann_1221)&
*/
