void foo (int x)
  requires x < 0
  ensures true; // SHOULD FAIL
{
  if (x < 0)
    assert(x >= -1) assume true; // MAY ERR
  else return;
}
