void loop()
  requires Loop
  ensures false;

int g(int x) 
  infer [@term]
  requires true
  ensures true;
{
   return x+1;
}

void hhh(int x) 
  infer [@term]  requires true ensures true;
{
   if (x < 0) return;
   else if (x<6) /* changing to 6 is OK */
     hhh(g(x));
   else hhh(x);
}


void main ()
  infer [@term]
  requires true
  ensures true;
{
  int x;
  x = 2;
  hhh(x);
}

/*
# cex-1e.ss --svcomp-compete

Termination Inference Result:
g:  requires emp & Term[34,1]
     ensures emp & x=res-1;
Termination Inference Result:
hhh:  case {
  x<=(0-1) -> requires emp & Term[38,1]
     ensures emp & true; 
  0<=x & x<=5 -> requires emp & MayLoop[]
     ensures emp & true; 
  6<=x -> requires emp & Loop{ 19:8}[]
     ensures false & false; 
  }
Termination Inference Result:
main:  requires emp & MayLoop[]
     ensures emp & true;


This example works nicely. Kudos!
Automatic addition of @post_n works!

 !!! @post is added into [g$int] for hhh$int


   if (x < 0) return;
   else if (x<6) /* changing to 6 is OK */
     hhh(g(x));
   else hhh(x);


g:  requires emp & Term[34,1]
     ensures emp & x=res-1;

hhh:  case {
  x<=(0-1) -> requires emp & Term[38,1]
     ensures emp & true; 
  0<=x -> requires emp & Loop{ 19:8}[]
     ensures false & false; 
  }

main:  requires emp & Loop{ 30:2, 19:8}[]
     ensures false & false;




 */
