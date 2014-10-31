relation nondet_bool(bool x).

void loop()
  requires Loop
  ensures false;

bool nondet()
  requires Term
  ensures nondet_bool(res);
  
void f(int x)
  infer [@term]
  requires true
  ensures true;
{
  if (x < 0) return;
  else {
    bool b = //true //
       nondet()
    ;
    dprint;
    if (b)
      f(x + 1);
    else
      return;
  }
}

/*
# cex-3.ss

Termination Inference Result:
f:  case {
  x<=(0-1) -> requires emp & Term[34,1]
     ensures emp & true; 
  0<=x -> requires emp & MayLoop[]
     ensures emp & true; 
  }

*/

/*
void g(int x) 
//infer [@term]  requires true ensures true;
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
  g(x);
}
*/
