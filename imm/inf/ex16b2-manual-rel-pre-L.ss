
/*
Immutability Annotation Inference
Precondition
*/

data cell {
 int fst;
 int snd;
}

relation P(ann a).
int simple_read_write(cell c)
  infer [P]
  requires c::cell<f,h>@b & P(b)
  ensures c::cell<g,h>@a;
{
  int i = c.fst + 1;
  return i;
}

