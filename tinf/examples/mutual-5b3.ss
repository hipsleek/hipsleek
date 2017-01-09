int f(int x)
  infer [ @term
  ]
//requires true ensures true;
/*
case {
    x <= 0 -> requires Term ensures true;
    x > 0 -> requires true ensures true;
  }
*/
case {
    x <= 0 -> requires Term ensures true;
    x > 0 & x<= 3 -> requires true ensures true;
    x > 3 & x<=8 -> requires true ensures true;
    x >10 -> requires true ensures true;
  }
{
  if (x <= 0) return 0;
  else if (x<=10) return f(x-1);
  else if (x>20) return f(x + 1);
  else if (rand_bool()) return 0;
  else return f(x);
}

/*
# mutual-5b3.ss

Problems:
 (i) Can termination ranking cases be combined?

Termination Inference Result:
f:  case {
  x<=0 -> requires emp & Term[32]
 ensures false & false; 
  1<=x & x<=3 -> requires emp & Term[32,3,-1+(1*x)]
 ensures emp & true; 
  4<=x & x<=8 -> requires emp & Term[32,4,-5+(1*x)]
 ensures emp & true; 
  21<=x -> requires emp & Loop[]
 ensures false & false; 
  11<=x & x<=20 -> requires emp & MayLoop[]
 ensures emp & true; 
  9<=x & x<=10 -> requires false & false 
  }


*/
