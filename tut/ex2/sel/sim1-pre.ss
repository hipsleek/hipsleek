relation P(int n).

void posint(int n)
  requires n>0  ensures true;

void foo(int n)
  infer [P]
  requires P(n)
  ensures true;
{
  posint(n); // assert n>0 assume n>0;
}

