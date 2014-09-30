void mayloop ()
  requires MayLoop
  ensures true;

void f (int x)
  infer [@term]
  requires true
  ensures true;
{
  if (x <= 0) return;
  else {
    mayloop();
    f(x - 1);
  }
}