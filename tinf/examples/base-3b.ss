bool rand()
  requires Term
  ensures true;

void f(int x)
  infer [@term]
  requires x > 0
  ensures true;
{
  if (rand()) return;
  else f(x + 1);
}