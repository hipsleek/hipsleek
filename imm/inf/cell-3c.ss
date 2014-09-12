data cell{
 int fst;
}

relation P1(ann v1).
relation P2(ann v1).

void foo(cell c)
  infer [P1,P2]
  requires c::cell<v>@a & P1(a)
  ensures c::cell<v>@b & P2(b)  ;
{
  int j = c.fst;
}
/*
# cell-3c.ss

Why is there a check 1 fail?

Checking procedure foo$cell... check 1 fail

!!! >>>>>> HIP gather infer pre <<<<<<
!!!Inferred Heap: []
!!!Inferred Pure: [ true]
Procedure foo$cell SUCCESS.
Stop Omega... 18 invocations 
0 false contexts at: ()

c::cell<v>@a & P1(a) |- c::cell<w>@L



*/
