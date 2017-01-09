data cell{
 int fst;
}

relation P(ann v1).
//relation P3(ann v1, int v,int r, int s).


int foo2(cell c)
//  infer [P,@term]
//  infer [@term]
  infer [@post_n]
//  infer [P]
  requires c::cell<v>@M
  ensures c::cell<w>@b;
{
  int x = c.fst;
  if (x>0) c.fst = 5;
  return x;
}


/**
In ex15c1, when infer[@imm_post]:
 es_infer_vars: [P__1434]
 es_infer_vars_rel: []

In ex15c2, when infer[@P]:
es_infer_vars_rel: [P]

*/
