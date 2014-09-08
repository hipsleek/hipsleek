int f(int x)
  infer [@term]
//requires true ensures true;
  case {
    x <= 0 -> requires Term ensures true;
    x > 0 -> requires Loop ensures true;
  }
{
  if (x <= 0) return 0;
  else return f(x) + g(x + 1);
}

int g(int x)
  infer [@term]
  requires true
  ensures true;
{
  if (x <= 0) return 0;
  else return f(x - 1) + f(x - 2);
}
/*
# mutual-5b.ss
# case {
    x <= 0 -> requires Term ensures true;
    x > 0 -> requires Loop ensures true;
  }

Termination Inference Result:
g:  case {
  1<=x -> requires emp & MayLoop[]
 ensures emp & true; 
  x<=0 -> requires emp & Term[30,2]
 ensures emp & true; 
  }
f:  case {
  x<=0 -> requires emp & Term[30]
 ensures emp & true; 
  0<x -> requires emp & Loop[]
 ensures emp & true; 
  }

# mutual-5b.ss
# requires true ensures true;

g:  case {
  1<=x & 2<=x -> requires emp & Loop[]
 ensures false & false; 
  1<=x & x<=1 -> requires emp & Term[30,5]
 ensures emp & true; 
  x<=0 -> requires emp & Term[30,2]
 ensures emp & true; 
  }
f:  case {
  1<=x -> requires emp & Loop[]
 ensures false & false; 
  x<=0 -> requires emp & Term[30,1]
 ensures emp & true; 
  }


*/
