
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
//infer [P]
  requires c::sum<5>
  ensures  c::sum<5>;
{
  int tmp = c.fst;
  c.fst = c.snd;
  c.snd = tmp;
}
