data cell{
 int fst;
}

relation P1(ann v1).
relation P2(ann v1).

int foo(cell c)
  infer [w]
  requires c::cell<v>@w 
  ensures c::cell<v>@z & v=res ;
{
  return c.fst;
}
