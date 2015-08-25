data cell{
 int fst;
}

relation P1(ann v1).
  relation P2(ann v1, ann v2).

void foo(cell c)
  infer [P1,P2]
  requires c::cell<v>@a & P1(a)
     ensures c::cell<v>@b & P2(a,b)  ;
{
  int j = c.fst;
}
/*
# cell-3c.ss

[RELASS [P1]: ( P1(a)) -->  a<:@L,
RELDEFN P2: ( b_1456=a & a<:@L & P1(a)) -->  P2(a,b_1456)]

  infer [P1,P2]
  requires c::cell<v>@a & P1(a)
     ensures c::cell<v>@b & P2(a,b)  ;


# why is cell missing in post-cond
# can we do a re-verify?

Post Inference result:
foo$cell
 EBase exists (Expl)[](Impl)[a; v](ex)[]c::cell<v>@L&a<:@L & a<:@L & 
       MayLoop[]&{FLOW,(4,5)=__norm#E}[]
         EAssume 
           (exists v_1455,b_1456: emp&v_1455=v & b_1456=a & a<:@L&
           {FLOW,(4,5)=__norm#E}[]

Checking procedure foo$cell... check 1 fail


*/
