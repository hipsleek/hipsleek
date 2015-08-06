
/*
Immutability Annotation Inference
Precondition
*/

data cell {
 int fst;
 int snd;
}

sum<s> == self::cell<a,b> & s=a+b
  inv true;

relation P (ann a). 

void simple_read_write(cell c)
  infer [P]
  requires c::cell<f@a,h> &P(a)
  ensures c::cell<g,h> & (g = f + 1);
{
  c.fst = c.fst + 1;
}
