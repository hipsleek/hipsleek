// this is now to specify the min stack required
// by a given method; it is specified in the post-condition

pred_prim RSteps<low:int,high:int>
  inv low<=high & high>=1;

/*
lemma "R split" self::RSteps<a> & p,r>=0 & a=p+r 
 <-> self::RSteps<p> * self::RSteps<r> ;
*/

global RSteps rs;


void sub_call()
  requires rs::RSteps<a,b> 
  ensures rs'::RSteps<a-1,b-1>; //'

bool rand()
 requires true
 ensures res or !res;

void p()
  requires rs::RSteps<a,m> & m>=4
  ensures  rs'::RSteps<b,k> & a-b>=1 & m-k<=4;//' 
  //at least one steps.
  //at most four steps.
{
  sub_call();
  if (rand()) f();
}
void f() 
  requires rs::RSteps<a,m> & m>=3
  ensures  rs'::RSteps<b,k> & a-b>=2 & m-k<=3;//' 
  //at least two steps.
  //at most three steps.
{
  sub_call(); //subtract current call
  dprint;
  g(); 
  if (rand()) h(); 
}

void g() 
  requires rs::RSteps<n,m> & m>=1
  ensures  rs'::RSteps<n-1,m-1>;//'
{
  sub_call(); //subtract current call
}

void h() 
  requires rs::RSteps<a,m> & m>=1
  ensures  rs'::RSteps<a-1,m-1>; //'
{
  sub_call(); //subtract current call
}

data node {
  node next;
}

ll<n> == self=null & n=0
  or self::node<q>*q::ll<n-1>
inv n>=0;

int length(node x) 
  requires x::ll<n>@L * rs::RSteps<a,m> & m>=n+1
  // at least n+1 steps available
  ensures  rs'::RSteps<a-(n+1),m-(n+1)> & res=n; //'
  // exactly n+1 steps
{
  sub_call(); //subtract current call
  if (x==null) return 0;
  else {
      return 1+length(x.next);
  }
}


