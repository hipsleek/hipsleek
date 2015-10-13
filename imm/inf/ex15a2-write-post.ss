
data cell{
 int fst;
}

//relation P3(ann v1, int v,int r, int s).

// relation P(ann v).

relation QQQ(ann v,ann v2).

  int foo2(cell c, cell d)
  infer [QQQ]
  requires c::cell<yyy>@a1 * d::cell<zzz>@M & QQQ(a1,@M)
  ensures c::cell<w>@a2 * d::cell<zzz>@a3;
{
  int x = c.fst;
  if (x>0) c.fst = 5;
  return x;
}
