data cell {
  int val;
}

void main(cell x, cell y)
  infer[@shape]
  requires true
  ensures true;
{
  while (y.val<x.val) 
    infer[@shape]
      requires true
      ensures true;
  {
    y.val = y.val+1;
  }
}
/*
# cell.ss 

  while (y.val<x.val) 
    infer[@shape]
      requires true
      ensures true;

What @shape spec is being composed for
while loop? Can we print it?

Checking procedure f_r_1200_while_10_2$cell~cell... Proving binding in method f_
r_1200_while_10_2$cell~cell for spec  EAssume ref [x;y]
   emp&{FLOW,(4,5)=__norm}[]
   , Line 0

( []) bind: node  y'::cell<val_10_1205'>@L cannot be derived from context
cell.ss_10:9_10:14

(


*/
