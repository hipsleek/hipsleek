
data cell{
 int fst;
}

relation P(ann v,ann w).

int foo2(cell c, cell d)
  infer [P]
  requires c::cell<_>@a1 * d::cell<_>@a2 & P(a1,a2)
  ensures c::cell<_> * d::cell<_>;
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
(FIXED)

Post Inference result:
foo2$cell~cell
EBase 
exists (Expl)[](Impl)[a1; Anon_11; a2; 
                      Anon_12](ex)[]c::cell<Anon_11>@a1 * (emp)&a1=@M & a2=@A & MayLoop[]&
{FLOW,(4,5)=__norm#E}[]
EAssume 
(exists Anon_1210,Anon_1211,ann_1229,
        ann_1228: c::cell<Anon_1210>@ann_1228 * d::cell<Anon_1211>@ann_1229&
        {FLOW,(4,5)=__norm#E}[]

*/
