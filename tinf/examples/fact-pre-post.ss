relation PP(int x, int r).
relation Q(int x).

int fact(int x)
  infer [PP,Q]
  requires Q(x) 
  ensures //true
  PP(x,res)
  ;
{
  assert x>=0;
  if (x==0) return 1;
  else return 1 + fact(x - 1);
}
/*
# fact.ss

 static  EList :EInfer [x]

How come @term not captured? 
*/
