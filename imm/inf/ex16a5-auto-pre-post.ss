
/*
Immutability Annotation Inference
Precondition
*/

data cell {
 int fst;
 int snd;
}

void simple_read_write(cell c)
  infer [@imm_pre,@imm_post]
  requires c::cell<f,h>
  ensures c::cell<g,h> & (g = f + 1);
{
  c.fst = c.fst + 1;
}


void simple_read_write3(cell c)
  infer [@imm_post]
  requires c::cell<f,h>@a
  ensures c::cell<g,h> & (g = f + 1);
{
  c.fst = c.fst + 1;
}
