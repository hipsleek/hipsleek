

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


void hoo1()
  infer [@pre_must] requires false
  ensures true ;

void goo1()
  requires true
  ensures true & flow __Error;
{
  hoo1();
  dprint;
}

void hoo2()
  requires false
  ensures true ;

void goo2()
  requires true
  ensures true & flow __Error;
{
  hoo2();
  dprint;
}

