data cell{
 int fst;
}
  int foo2(cell c, cell d)
  infer [@imm_post]
  requires c::cell<yyy>@M
    ensures c::cell<w>;
{
  int x = c.fst;
  if (x>0) c.fst = 5;
  return x;
}
