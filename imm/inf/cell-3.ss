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


  P1(a) --> a<:@M
  a<:@M & a<:b --> P2(a,b) 


  P1(a) :- a=@M
  P2(a,b) :- a=@M & a=b


 requires c::cell<v>@M
 ensures  c::cell<2>@M;



# cell-2.ss

# Why b is free?
# Why did not infer for P1?

!!!WARNING : uninterpreted free variables [b] in specification.
Checking procedure foo$cell... check 1 fail

!!! >>>>>> HIP gather infer pre <<<<<<
!!!Inferred Heap: []
!!!Inferred Pure: [ true]

Expect:
  a<:@M &

*/
