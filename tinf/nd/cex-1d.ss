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

void hhh(int x) 
  infer [@term]  requires true ensures true;
{
   if (x < 0) return;
   else if (x<7) /* changing to 6 is OK */
      hhh(x+1);
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
# cex-1d.ss

I think this is a good example, but we can
fix it later when we have time in a more general way?

void hhh(int x) 
  infer [@term]  requires true ensures true;
{
   if (x < 0) return;
   else if (x<7) /* changing to 6 is OK */
      hhh(x+1);
   else hhh(x);
}

I guess this is an imprecision of termination
inference which gave MayLoop instead of Loop for n<7.
For n<6, it gave correct Loop result.
I believe this aspect could be improved.

hhh:  case {
  x<=(0-1) -> requires emp & Term[38,1]
     ensures emp & true; 
  0<=x & x<=2 -> requires emp & MayLoop[]
     ensures emp & true; 
  3<=x -> requires emp & Loop{ 21:8}[]
     ensures false & false; 
  }


g:  requires emp & Term[34,1]
     ensures emp & x=res-1;

Termination Inference Result:
main:  requires emp & MayLoop[]
     ensures emp & true;

 */
