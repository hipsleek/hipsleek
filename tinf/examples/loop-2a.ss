void loop ()
  requires Loop
  ensures true;

void f (int x)
  infer [@term]
  requires true
  ensures true;
{
  if (x <= 0) return;
  else {
    loop();
    f(x + 1);
  }
}