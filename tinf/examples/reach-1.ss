void term()
  requires Term
  ensures true;

void f(int x)
  infer [@term]
  requires true
  ensures true;
{
  term();
}