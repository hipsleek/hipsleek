void loop()
  requires Loop
  ensures false;

int g(int x) 
  infer [@term,@post_n]
  requires true
  ensures true;
{
   return x+1;
}

void h(int x) 
  infer [@term]
  requires true
  ensures true;
{
   if (x < 0) return;
   else if (x<10)
      h(g(x));
   else h(x);
}


void main ()
  infer [@term]
  requires true
  ensures true;
{
  int x;
  x = 2;
  h(x);
}

/*
# cex-1c.ss

I guess this is an imprecision of termination
inference which gave MayLoop instead of Loop.
I believe it could be improved.

void h(int x) 
  infer [@term]
  requires true
  ensures true;
{
   if (x < 0) return;
   else if (x<10)
      h(g(x));
   else h(x);
}

Termination Inference Result:
h:  case {
  x<=(0-1) -> requires emp & Term[38,1]
     ensures emp & true; 
  0<=x & x<=5 -> requires emp & MayLoop[]
     ensures emp & true; 
  6<=x -> requires emp & Loop{ 21:8}[]
     ensures false & false; 
  }

g:  requires emp & Term[34,1]
     ensures emp & x=res-1;

Termination Inference Result:
main:  requires emp & MayLoop[]
     ensures emp & true;

 */
