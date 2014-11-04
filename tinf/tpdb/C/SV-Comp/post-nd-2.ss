void main()
{
  int x;
  while (x > 0 && (__VERIFIER_nondet_int() > 0)) 
    infer [@post_n]
    requires true
    ensures true;
  {
    x = x - 1;
  }
}

bool nondet()
  requires true
  ensures true;
