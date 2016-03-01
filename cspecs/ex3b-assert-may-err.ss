void foo (int x)
  requires x < 0
  ensures true & flow __MayError;
{
  if (x < 0)
    assert(x >= -1); // MAY ERR
  else return;
}
