bool nondet()
  requires Term
  ensures true;

void f(int x)
  infer [@term]
  requires true
  ensures true;
{
  if (x < 0) return;
  else {
    if (nondet())
      f(x + 1);
    else
      f(x + 4);
  }
}


void main ()
  infer [@term]
  requires true
  ensures true;
{
  int x;
  f(x);
}

/*
  OK

*/
