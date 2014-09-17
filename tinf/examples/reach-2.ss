void loop()
  requires Loop
  ensures false;

void f(int x)
  infer [@term]
  requires true
  ensures true;
{
  loop();
}