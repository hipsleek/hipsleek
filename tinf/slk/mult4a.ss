void f(int x)
  infer [@term]
  requires true
  ensures true;
{
  if (x < 0) return;
  else {
    f(x - 1);
    dprint;
    f(x + 1);
    dprint;
  }
}

  
