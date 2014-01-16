/*
  hip steps-loop.ss --en-inf

  RSteps captures the min/max number of calls to user-defined
  functions
*/

pred_prim RSteps<low:int,high:int>
  inv low<=high & high>=0;

/*
   A terminating program uses at most finite steps.
   A non-terminating program uses infinite steps.
   A possibly non-terminating program 
      needs possibly infinite steps.

   Term = RSteps<a,m> & m<\inf

    RSteps<a,b> & m<\inf 
    {..}
    RSteps<c,d> & a-c>=0

   Loop = RSteps<a,m> & a=\inf & m=\inf 

    RSteps<a,b> & b=\inf 
    {..}
    RSteps<c,d> & a-c>=\inf

   MayLoop = RSteps<a,m> & m=\inf 
    RSteps<a,b> & b=\inf 
    {..}
    RSteps<c,d> & a-c>=0
*/

global RSteps rs;

void sub_call()
  requires rs::RSteps<a,b> 
  ensures rs'::RSteps<a-1,b-1>; //'

bool rand()
 requires true
 ensures res or !res;

data node {
  node next;
}

ll<n> == self=null & n=0
  or self::node<q>*q::ll<n-1>
inv n>=0;

int length(node x) 
  requires x::ll<n>@L * rs::RSteps<a,m> & m>=n+1 & m<\inf
  // at least n+1 steps available & <\inf for terminating code
  ensures  rs'::RSteps<a-(n+1),m-(n+1)> & res=n; //'
  // exactly n+1 steps
{
  sub_call(); //subtract current call
  if (x==null) return 0;
  else {
      return 1+length(x.next);
  }
}

void loop() 
  requires rs::RSteps<a,b> & b=\inf 
  ensures  rs'::RSteps<c,b> & a-c>=\inf; //'
  // at least infinity steps
{
  sub_call(); //subtract current call
  loop();
}

void mayloop() 
  requires rs::RSteps<a,b> & b=\inf 
  ensures  rs'::RSteps<c,b> & a-c>=0; //'
  // at least infinity steps
{
  sub_call(); //subtract current call
  if (rand()) mayloop();
}


