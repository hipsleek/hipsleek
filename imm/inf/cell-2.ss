data cell{
 int fst;
}

relation P1(ann v1, ann v2).
relation P2(ann v1).

int foo(cell c)
  infer [P1]
  requires c::cell<v>@a & P1(a,b)
  ensures c::cell<v>@b & v=res ;
{
  return c.fst;
}
/*

# cell-1.ss

Why is the a failure?

Checking procedure foo$cell... check 1 fail

!!! >>>>>> HIP gather infer pre <<<<<<
!!!Inferred Heap: []
!!!Inferred Pure: [ w<:@L, w<:@L]
*/
