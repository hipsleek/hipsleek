bool nondet ()
  requires Term
  ensures true;
  
void f(int x)
  infer [@term]
  requires true
  ensures true;
{
  if (x < 0) return;
  else {
    f(x + 1);
    f(x - 1);
  }
}
