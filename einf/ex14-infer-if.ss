relation P(int x).

void foo(int x)
  infer [P] //,@err_must]
  requires P(x)
  ensures true & flow __flow;
{
  if (x>0)
   assert x'>3 assume true;
}


/*
# ex14.ss

*************************************
******pure relation assumption*******
*************************************
[RELASS [P]: ( P(x)) -->  x!=1 & x!=2 & x!=3]
*************************************

*/
