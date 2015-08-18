
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

void simple_read_write(cell c)
//  infer [@imm_pre,@imm_post]
  infer [@imm_pre]
  requires c::cell<f,h>
  ensures c::cell<g,h> & (g = f + 1); 
  infer [@imm_pre]
  requires c::sum<n> 
  ensures c::sum<n+1>;  
{
  c.fst = c.fst + 1;
}
