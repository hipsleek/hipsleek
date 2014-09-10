void f(int x)
  infer [@term]
  requires Loop 
  ensures true;
{
  if (x <= 0) return;
  else return f(x);
}