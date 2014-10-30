void loop()
  requires Loop
  ensures false;

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
    if (true)
      f(x + 1);
    else
      return;
  }
}

void g(int x) 
  infer [@term]
  requires true
  ensures true;
{
   if (x > 0)
      f(x);
}

void main ()
  infer [@term]
  requires true
  ensures true;
{
  int x;
  x = 1;
  g(x);
}

/*

Termination Inference Result:
main:  requires emp & MayLoop[]


*/
