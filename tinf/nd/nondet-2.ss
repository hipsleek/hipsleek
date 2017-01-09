void loop()
  requires Loop
  ensures false;
  
bool nondet()
  requires Term
  ensures true;
  
void f(int x)
  infer [@term]
  requires true
  ensures true;
{
  if (x < 0) return;
  else if (nondet())
    loop();
  else f(x + 1);
}