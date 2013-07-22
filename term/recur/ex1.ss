void foo(ref int x)
 case {
  x<=0 -> requires Term[] ensures true;
  x>0 -> requires Term[] ensures true;
}
{
  if (x>0) {
      x = -2*x;
      foo(x);
  }
}
