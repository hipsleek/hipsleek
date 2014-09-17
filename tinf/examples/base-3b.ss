void f(int x) 
  infer [@term]
  case {
    x <= 0 -> requires false ensures false;
    x > 0 -> requires true ensures true;
  }
{
  if (x <= 0) 
    return;
  else
    f(x + 1);
}