
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
 infer []
  requires c::cell<f,h>@M
  ensures c::cell<g,h>@a & P(a) & (g = f + 1);
{
  c.fst = c.fst + 1;
}

