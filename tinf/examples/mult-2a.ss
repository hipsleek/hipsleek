bool nondet ()
  requires Term
  ensures true;
  
void f(int x, int y)
  infer [@term]
  requires true
  ensures true;
{
  if (x < 0) return;
  else {
    if (nondet ()) f(x - y, y);
    else f(x + y, y);
  }
}
