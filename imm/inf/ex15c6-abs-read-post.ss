
data cell{
 int val;
}

relation Q(ann a1, ann a2).

  int foo2(cell c,cell d)
  infer [Q]
  requires c::cell<_>@L * d::cell<_>@A 
  ensures c::cell<_>@b1 * d::cell<_>@b2 & Q(b1,b2);
{
  int x = c.val;
  return x;
}

/*
# ex15c6.ss

Post Inference result:
foo2$cell~cell
 EBase 
   exists (Expl)[](Impl)[Anon_11; Anon_12](ex)[]c::cell<Anon_11>@L * (emp)&
   MayLoop[]&{FLOW,(4,5)=__norm#E}[]
   EAssume 
     (exists Anon_1205,Anon_1206,b1_1207,b2_1208: (emp) * (emp)&b2_1208=@A & 
     b1_1207=@A&{FLOW,(4,5)=__norm#E}[]

# Nice though d::cell<..> need not be removed from pre.
# Can we use an option to control such removal.

*/
