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
      f(x + 6);
    else
      f(x + 4);
  }
}

void g(int x)
  infer [@term]
  requires true
  ensures true;
{

  if (x > 1) f(x);
  else g(x+1);
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
  Expect Loop but return MayLoop

*/
