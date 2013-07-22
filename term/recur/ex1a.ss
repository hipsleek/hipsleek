void foo(ref int x)
 requires TermRec[?]
  ensures true;
{
  if (x>0) {
      x = -2*x;
      foo(x);
  }
}
