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
  d.val = x;
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

[RELASS [Q]: ( Q(a1,a2)) -->  (a2=@M | a1=@A),
 RELASS [Q]: ( Q(a1,a2)) -->  a1<:@L]

id: 2; caller: []; line: 13; classic: false; kind: BIND; hec_num: 1; evars: []; infer_vars: [ Q]; c_heap: emp; others: [] globals: [@dis_err]
 checkentail c::cell<Anon_11>@a1 * d::cell<Anon_12>@a2&Q(a1,a2) & d'=d & c'=c & a1<:@L & 
x'=Anon_11 & MayLoop[]&{FLOW,(4,5)=__norm#E}[]
 |-  d'::cell<val_13_1199'>@M&{FLOW,(1,29)=__flow#E}[]. 
pure rel_ass: [RELASS [Q]: ( Q(a1,a2)) -->  (a2=@M | a1=@A)]
ho_vars: nothing?
res:  1[
    c::cell<Anon_11>@a1&Q(a1,a2) & d'=d & c'=c & a1<:@L & x'=Anon_11 & 
val_13_1199'=Anon_12&{FLOW,(4,5)=__norm#E}[]
   ]

---------------------------------------

 EInfer []
   EBase 
     exists (Expl)[](Impl)[a1; Anon_11; a2; 
     Anon_12](ex)[]c::cell<Anon_11>@a1 * d::cell<Anon_12>@a2&a2=@M & a1=@L & 
     MayLoop[]&{FLOW,(4,5)=__norm#E}[]
     EAssume 
       (exists b1_1208,Anon_1209,b2_1210,
       Anon_1211: c::cell<Anon_1209>@b1_1208 * d::cell<Anon_1211>@b2_1210&
       {FLOW,(4,5)=__norm#E}[]Stop Omega... 180 invocations 


*/
