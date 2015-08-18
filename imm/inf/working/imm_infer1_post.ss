/*
Immutability Annotation Inference
Precondition
*/

data cell {
 int fst;
 int snd;
}

int simple_read_only(cell c)
  infer [@imm_post]
  requires c::cell<f,g>@L
  ensures c::cell<f,g> & res = (f + g + 1);
{
  int x = c.fst;
  int y = c.snd;
  x = x + 1;
  return x + y;
}


void simple_read_write(cell c)
  infer [@imm_post]
  requires c::cell<f,_>@M
  ensures c::cell<g,_> & (g = f + 1);
{
  c.fst = c.fst + 1;
}
