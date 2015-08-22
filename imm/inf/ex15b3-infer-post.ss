data cell{
 int fst;
}

relation P(ann v).

  int foo2(cell c, cell d)
  infer [P]
  requires c::cell<yyy>@M
  ensures c::cell<w>@b & P(b);
{
  int x = c.fst;
  if (x>0) c.fst = 5;
  return x;
}
