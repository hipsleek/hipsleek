data cell{
 int fst;
}

relation P(ann v1).
//relation P3(ann v1, int v,int r, int s).


int foo2(cell c)
//  infer [P,@term]
//  infer [@term]
//  infer [@imm_post]
  infer [@post_n]
  requires c::cell<v>@M
  ensures c::cell<w>@b   ;
{
  int x = c.fst;
  if (x>0) c.fst = 5;
  return x;
}

