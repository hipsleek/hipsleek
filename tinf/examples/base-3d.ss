void loop ()
  requires Loop
  ensures true;

void f(int x) 
  infer [@term]
  requires true
  ensures true;
{
  if (x <= 0) 
    loop();
  else
    f(x + 1);
}