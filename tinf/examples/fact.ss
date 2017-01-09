int fact(int x)
  infer [@term,x]
  requires true
  ensures //true
  res >= 1
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
