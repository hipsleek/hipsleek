void foo (int x)
  requires x < 0
  ensures true & flow __Error;
{
  if (x < 0)
    assert(x >= 0); // MUST ERR
  else return;
}
