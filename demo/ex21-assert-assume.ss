void foo(int x)
  requires true
  ensures true;
{
  if (x>0) {
    assert false assume true;
    assert false;
    assert x'<0;
  }
}
