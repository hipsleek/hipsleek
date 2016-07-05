
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
  return x;
}

/*
# ex15b6.ss

Given below. 

  infer [Q]
  requires c::cell<_>@a1 * d::cell<_>@a2 & Q(a1,a2)
  ensures c::cell<_>@b1 * d::cell<_>@b2;
{
  int x = c.val;
  return x;
}

GOT

!!! **infer.ml#1367:RelInferred (rel_ass):[RELASS [Q]: ( Q(a1,a2)) -->  a1<:@L]
!!! **typechecker.ml#834:WARNING : Spurious RelInferred (not collected):[RELASS [Q]: ( Q(a1,a2)) -->  a1<:@L]

# Why is it spurious?

# What happen to a2=@A?

[ EInfer [Q]
   EBase 
     exists (Expl)[](Impl)[a1; Anon_11; a2; 
     Anon_12](ex)[]c::cell<Anon_11>@a1 * d::cell<Anon_12>@a2&a1=@L&
     {FLOW,(4,5)=__norm#E}[]
     EBase 
       emp&MayLoop[]&{FLOW,(4,5)=__norm#E}[]
       EAssume 
         (exists b1_1207,Anon_1208,b2_1209,
         Anon_1210: c::cell<Anon_1208>@b1_1207 * d::cell<Anon_1210>@b2_1209&
         {FLOW,(4,5)=__norm#E}[]]


*/
