
data cell{
 int fst;
}

relation Q(ann v).

int foo2(cell c, cell d)
infer [@imm_pre]
  requires c::cell<_> * d::cell<_>
  ensures c::cell<_> * d::cell<_>;
{
  int x = c.fst;
  if (x>0) c.fst = 5;
  return x;
}

/*
# ex15b1.ss

Given below. 

infer [@imm_pre]
  requires c::cell<_> * d::cell<_>
  ensures c::cell<_> * d::cell<_>;

I think you should first form:

infer [U]
  requires c::cell<_>@a1 * d::cell<_>@a2 & U(a1,a2)
  ensures c::cell<_>@a3 * d::cell<_>@a4;

And then try to obtain:

  requires c::cell<_>@M * d::cell<_>@A
  ensures c::cell<_>@a3 * d::cell<_>@a4;

*/
