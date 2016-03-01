void foo (int x)
  requires x < 0
  ensures true ; // SHOULD SUCCESS
{
  if (x < 0) {
    assert(x >= 0) assume true; // MUST ERR
    dprint;
  }
  else return;
}
