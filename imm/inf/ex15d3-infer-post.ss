data cell{
 int fst;
}

//relation P(int x, int y).

  int foo2(cell c, cell d)
  infer [@term]
  requires c::cell<yyy> & yyy>2
    ensures c::cell<w> ;
{
  int x = c.fst;
  if (x>0) c.fst = 5;
  return x;
}
