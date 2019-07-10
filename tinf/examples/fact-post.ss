relation P(int x, int r).

int fact(int x)
  infer [P]
  requires true
  ensures //true
  P(x,res)
  ;
{
  if (x==0) return 1;
  else return 1 + fact(x - 1);
}
/*
# fact.ss

 static  EList :EInfer [x]

How come @term not captured? 
*/
