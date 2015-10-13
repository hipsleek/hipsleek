
data cell{
 int val;
}

relation Q(ann a1, ann a2).

  int foo2(cell c,cell d)
  infer [Q]
  requires c::cell<_>@a1 * d::cell<_>@a2 & Q(a1,a2)
  ensures c::cell<_>@b1 * d::cell<_>@b2;
{
  int x = c.val;
  c.val = x+1;
  return x;
}

/*
# ex15b8.ss

# need to make a2=@A explicit.

Post Inference result:
foo2$cell~cell
 EBase 
   exists (Expl)[](Impl)[a1; Anon_11; a2; 
   Anon_12](ex)[]c::cell<Anon_11>@a1 * d::cell<Anon_12>@a2&a1=@M & MayLoop[]&
   {FLOW,(4,5)=__norm#E}[]
   EAssume 
     (exists b1_1213,Anon_1214,b2_1215,
     Anon_1216: c::cell<Anon_1214>@b1_1213 * d::cell<Anon_1216>@b2_1215&
     {FLOW,(4,5)=__norm#E}[]

*/
