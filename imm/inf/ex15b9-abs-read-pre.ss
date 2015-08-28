data cell{
 int val;
}

relation Q(ann a1, ann a2).

  int foo2(cell c,cell d)
  infer [Q]
  requires c::cell<_>@a1 * d::cell<_>@a2 & Q(a1,a2)
  ensures c::cell<_> * d::cell<_>;
{
  int x = c.val;
  d.val = x;
  return x;
}

/*
Result:
Normalize NOANN to fresh spec var

!!! **pi.ml#869:new_specs2:
[ EInfer [Q]
   EBase 
     exists (Expl)[](Impl)[a1; Anon_11; a2; 
     Anon_12](ex)[]c::cell<Anon_11>@a1 * d::cell<Anon_12>@a2&a2=@M & a1=@L&
     {FLOW,(4,5)=__norm#E}[]
     EBase 
       emp&MayLoop[]&{FLOW,(4,5)=__norm#E}[]
       EAssume 
         (exists Anon_1204,Anon_1205,ann_1223,
         ann_1222: c::cell<Anon_1204>@ann_1222 * d::cell<Anon_1205>@ann_1223&
         {FLOW,(4,5)=__norm#E}[]]
Post Inference result:
foo2$cell~cell
 EBase 
   exists (Expl)[](Impl)[a1; Anon_11; a2; 
   Anon_12](ex)[]c::cell<Anon_11>@a1 * d::cell<Anon_12>@a2&a2=@M & a1=@L & 
   MayLoop[]&{FLOW,(4,5)=__norm#E}[]
   EAssume 
     (exists Anon_1204,Anon_1205,ann_1223,
     ann_1222: c::cell<Anon_1204>@ann_1222 * d::cell<Anon_1205>@ann_1223&
     {FLOW,(4,5)=__norm#E}[]
*/
