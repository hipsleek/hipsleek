// this is now to specify the min stack required
// by a given method; it is specified in the post-condition

pred_prim RMin<low:int>
  inv true;

/*
lemma "R split" self::RMin<a> & p,r>=0 & a=p+r 
 <-> self::RMin<p> * self::RMin<r> ;
*/

global RMin s_min;


void sub_call()
  requires s_min::RMin<a> 
  ensures s_min'::RMin<a+1>; //'

bool rand()
 requires true
 ensures res or !res;

void f() 
  requires s_min::RMin<a> 
  ensures  s_min'::RMin<b> & b-a>=2;//' at least two steps.
{
  sub_call(); //add stack frame used
  dprint;
  g(); 
  if (rand()) h(); // a bit slow when this is added
}

void g() 
  requires s_min::RMin<n> 
  ensures  s_min'::RMin<n+1>;//'
{
  sub_call(); //add stack frame used
}

void h() 
  requires s_min::RMin<a> 
  ensures  s_min'::RMin<a+1>; //'
{
  sub_call(); //add stack frame used
}


/*
Why did we have?

 checkentail Base s_min_16::RMin<flted_17_979>@M&a=a_968 & 0<=a & flted_17_979=1+a_968 & 
0<=a_968&{FLOW,(24,25)=__norm}[]
 |-  Base s_min_16'::RMin<n>@M&{FLOW,(24,25)=__norm}[]. 

*/
