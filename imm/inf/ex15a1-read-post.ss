
data cell{
 int fst;
}

relation Q(ann v).

int foo2(cell c, cell d)
infer [@imm_pre]
  requires c::cell<yyy> * d::cell<yyy>@A
  ensures c::cell<yyy>@b * d::cell<yyy>;
{
  int x = c.fst;
  if (x>0) c.fst = 5;
  return x;
}

/*
relation P(ann v1).
//relation P3(ann v1, int v,int r, int s).


int foo2(cell c)
  infer [@imm_post]
  requires c::cell<v>@M
  ensures c::cell<w>@b ;
{
  int x = c.fst;
  if (x>0) c.fst = 5;
  return x;
}


relation P(ann v1, ann v2).
//relation P3(ann v1, int v,int r, int s).


int foo2(cell c)
  infer [@imm_pre]
  requires c::cell<v>@a*y::cell<>*x::cell<>@L & P(a,b)
  ensures c::cell<w>;
{
  int x = c.fst;
  if (x>0) c.fst = 5;
  return x;
}
 
P(a,b) a=@M & b=@A

*/
