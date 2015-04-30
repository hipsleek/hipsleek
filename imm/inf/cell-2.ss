data cell{
 int fst;
}

relation P1(ann v1, ann v2).
relation P2(ann v1).

int foo(cell c)
  infer [P1]
  requires c::cell<v>@a & P1(a,b) 
  ensures c::cell<v>@b & v=res;
{
  return c.fst;
}
/*
# cell-2.ss

int foo(cell c)
  infer [P1]
  requires c::cell<v>@a & P1(a,b) 
  ensures c::cell<v>@b & v=res;
{
  return c.fst;
}

GOT
===
[RELASS [P1]: ( P1(a,b)) -->  a<:@L]

Post Inference result:
foo$cell
 EBase exists (Expl)[](Impl)[a; v](ex)[]c::cell<v>@L&a<:@L & MayLoop[]&
       {FLOW,(4,5)=__norm#E}[]
         EAssume 
           (exists v_1460: emp&v=res & v_1460=v&{FLOW,(4,5)=__norm#E}[]

# Why b is free?
# What happen to Cell in post

!!!WARNING : uninterpreted free variables [b] in specification.
Checking procedure foo$cell... check 1 fail

*/
