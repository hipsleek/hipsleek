
/*
Immutability Annotation Inference
Precondition
*/

data cell {
 int fst;
 int snd;
}

/*
int simple_read_only(cell c)
  infer [@imm_pre]
  requires c::cell<f,g>
  ensures res = (f + g + 1);
{
  int x = c.fst;
  int y = c.snd;
  x = x + 1;
  return x + y;
}
*/

relation P (ann a). 

void simple_read_write(cell c)
  infer [P]
  requires c::cell<f@a,h> &P(a)
  ensures c::cell<g,h> & (g = f + 1);
{
  c.fst = c.fst + 1;
}

