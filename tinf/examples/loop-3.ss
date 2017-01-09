void loop ()
  requires Loop
  ensures false;

void f (int x)
  infer [@term]
  requires true
  ensures true;
{
  if (x <= 0) return;
  else {
    loop();
    f(x - 1);
  }
}