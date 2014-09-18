void foo(int x, int y)
  infer [@term]
  case {
    x < 0 -> requires Term ensures true;
    x >= 0 -> requires true ensures true;
  }
{
  if (x < 0) return;
  else { 
    foo(x + y, y);
    //dprint;
    //return;
  }
}