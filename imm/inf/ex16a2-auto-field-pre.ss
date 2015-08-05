
/*
Immutability Annotation Inference
Precondition
*/

data cell {
 int fst;
 int snd;
}

void simple_read_write(cell c)
  infer [@imm_pre]
  requires c::cell<f,h>
  ensures c::cell<g,h> & (g = f + 1);
{
  c.fst = c.fst + 1;
}
