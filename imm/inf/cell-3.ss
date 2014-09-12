data cell{
 int fst;
}

relation P1(ann v1, ann v2).
relation P2(ann v1).

void foo(cell c)
  infer [P1]
  requires c::cell<v>@a & P1(a,b)
  ensures c::cell<2>@b  ;
{
  c.fst = 2;
}
/*

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
