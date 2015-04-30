data cell{
 int fst;
}

relation P2(ann v1, ann v2).
relation P1(ann v1).

void foo(cell c)
  infer [P1,P2]
  requires c::cell<v>@a & P1(a)
  ensures c::cell<2>@b & P2(a,b) ;
{
  c.fst = 2;
}

/*
void foo(cell c)
  infer [a,b]
  requires c::cell<v>@a
  ensures c::cell<2>@b  ;
{
  c.fst = 2;
}
*/
/*


 [RELASS [P1]: ( P1(a)) -->  a=@M,
RELDEFN P2: ( a=@M & b_1459=@M & P1(a)) -->  P2(a,b_1459)]
*************************************

Post Inference result:
foo$cell
 EBase exists (Expl)[](Impl)[a; v](ex)[]c::cell<v>@L&a=@M & a=@M & MayLoop[]&
       {FLOW,(4,5)=__norm#E}[]
         EAssume 
           (exists flted_11_1458,b_1459: emp&flted_11_1458=2 & a=@M & 
           b_1459=@M&{FLOW,(4,5)=__norm#E}[]


 requires c::cell<v>@M
 ensures  c::cell<2>@M;


# cell-2.ss


!!! >>>>>> HIP gather infer pre <<<<<<
!!!Inferred Heap: []
!!!Inferred Pure: [ true]

Expect:
  a<:@M &

*/
