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
    if (nondet ()) f(x - 1);
    else f(x + 1);
  }
}