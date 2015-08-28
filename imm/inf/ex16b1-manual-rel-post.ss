
/*
Immutability Annotation Inference
Precondition
*/

data cell {
 int fst;
 int snd;
}

relation P(ann a).

void simple_read_write(cell c)
  infer [P]
  requires c::cell<f,h>@M //& P(b)
  ensures c::cell<g,h>@a & P(a);
{
  c.fst = c.fst + 1;
}

