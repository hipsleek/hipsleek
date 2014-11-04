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
# cex-1a.ss


Termination Inference Result:
f:  case {
  x<=(0-1) -> requires emp & Term[33,1]
     ensures emp & true; 
  0<=x -> requires emp & Loop{ 17:6}[]
     ensures false & false; 
  }

Termination Inference Result:
g:  case {
  x<=0 -> requires emp & Term[37,1]
     ensures emp & true; 
  1<=x -> requires emp & Loop{ 29:6, 17:6}[]
     ensures false & false; 
  }

Termination Inference Result:
main:  requires emp & Loop{ 39:2, 29:6, 17:6}[]
     ensures false & false;



*/
