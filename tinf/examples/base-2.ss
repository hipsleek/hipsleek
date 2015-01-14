void term ()
  requires Term
  ensures true;

void f(int x) 
  infer [@term]
  requires true
  ensures true;
{
  if (x <= 0) 
    term();
  else
    f(x - 1);
}