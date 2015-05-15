void foo()
  requires true
  ensures true & flow __Error;
{
  assert false assume true;
  dprint;
}


/*
# ex23.ss

WARNING: ex23-or-simple.ss_3:10_3:30:the result type __Error#E is not covered by the throw list[__norm#E]

*/
