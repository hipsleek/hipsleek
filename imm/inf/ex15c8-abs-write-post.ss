
data cell{
 int val;
}

relation Q(ann a1, ann a2).

  int foo2(cell c,cell d)
  infer [Q]
  requires c::cell<_>@a1 * d::cell<_>@a2 & a1=@M & a2=@A
  ensures c::cell<_>@b1 * d::cell<_>@b2 & Q(b1,b2);
{
  int x = c.val;
  c.val = x+1;
  return x;
}

/*
# ex15c8.ss

# Good. Maybe can apply an extra step to remove the
  existential vars; after absent elimination.


foo2$cell~cell
 EBase 
   exists (Expl)[](Impl)[a1; Anon_11; a2; 
   Anon_12](ex)[]c::cell<Anon_11>@a1 * (emp)&a1=@M & a2=@A & MayLoop[]&
   {FLOW,(4,5)=__norm#E}[]
   EAssume 
     (exists Anon_1217,Anon_1218,b1_1219,
     b2_1220: c::cell<Anon_1217>@b1_1219 * (emp)&b2_1220=@A & b1_1219=@M&
     {FLOW,(4,5)=__norm#E}[]
Stop Omega... 75 invocations 


*/
