int fact(int x)
  infer [@term,x,@post_n]
  requires true
  ensures //true
  res >= 1
  ;
{
  if (x==0) return 1;
  else return 1 + fact(x - 1);
}
/*
# tinf/examples/fact-2.ss

 static  EList :EInfer [x]

How come @term,@post_n not captured? 
*/
