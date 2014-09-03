bool nondet ()
  requires Term
  ensures true;
  
void f(int x,bool b)
  infer [@term]
  requires true
  ensures true;
{
  if (x < 0) return;
  else {
    if (b) f(x - 1,b);
    else f(x + 1,b);
  }
}
  
/*
# mult4-2.ss

 our case-analysis work with boolean?

*/
