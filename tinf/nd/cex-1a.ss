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
    if (true)
      /* return; */
      f(x + 1);
    else
      /* f(x + 2); */
      return;
      /* loop(); */
  }
}


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

/*
# cex-1a.ss

void g(int x) 
//infer [@term]  requires true ensures true;

Why did g has an empty spec?
I guess the problem can be resolved by using --infer "@term"

f:  case {
  x<=(0-1) -> requires emp & Term[34,1]
     ensures emp & true; 
  0<=x -> requires emp & Loop{ 19:6}[]
     ensures false & false; 
  }

!!! Termination Inference is not performed due to empty set of relational assumptions.

Checking procedure g$int... 
Procedure g$int SUCCESS.

Termination Inference Result:
main:  requires emp & MayLoop[]
     ensures emp & true;

*/
/*

Termination Inference Result:
main:  requires emp & MayLoop[]

expect: line 32 -> line 18

*/
