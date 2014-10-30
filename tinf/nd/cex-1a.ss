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
    bool b = nondet();
    if (b) 
      f(x + 1);
    else
      /* f(x + 2); */
      return;
      /* loop(); */
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

Termination Inference Result:
main:  requires emp & MayLoop[]

expect: line 32 -> line 18

*/
