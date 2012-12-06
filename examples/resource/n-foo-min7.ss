// this is now to specify the min stack required
// by a given method; it is specified in the post-condition

pred_prim RS<low:int>
  inv low>=0;

pred_prim RS_min<low:int>
  inv low>=0;

pred_prim RS_max<high:int>
  inv hgh>=0;

global RS_max stk_max;
global RS_min stk_min;
global RS stk;

// add back space into stack
void add_stk(int n)
  requires stk::RS<a> & n>=0
  ensures stk::RS<a+n>;

void sub_stk(int n)
  requires stk::RS<a> & n>=0 & a>=n
  ensures stk::RS<a-n>;

void mark()
  requires stk::RS<a>@L
  ensures stk_min::RS_min<a> * stk_max::RS_max<a>;

bool rand()
 requires true
 ensures res or !res;


void f() 
  requires stk::RS<n>
  ensures  stk::RS<n> * stk_min::RS_min<m> 
    * stk_max::RS_max<h> & h<=n+5 & m>=n+5;
{
  add_stk(2); //add stack frame used
  mark();
  //g(); h();
  h(); g();
  //dprint;
  sub_stk(2); //add stack frame used
}

void f2() 
  requires stk::RS<n>
  ensures  stk::RS<n> * stk_min::RS_min<m> 
    * stk_max::RS_max<h> & h<=n+5 & m>=n+4;
{
  add_stk(2); //add stack frame used
  mark();
  if (rand()) h();
  else g();
  //dprint;
  sub_stk(2); //add stack frame used
}

void g() 
  requires stk::RS<n> 
  ensures  stk::RS<n> * stk_min::RS_min<m> 
    * stk_max::RS_max<h> & h<=n+2 & m>=n+2;
{
  add_stk(2); //add stack frame used
  mark();
  sub_stk(2); //add stack frame used
}

void h() 
  requires stk::RS<n> 
  ensures  stk::RS<n> * stk_min::RS_min<m> 
    * stk_max::RS_max<h> & h<=n+3 & m>=n+3;
{
  add_stk(3); //add stack frame used
  mark();
  sub_stk(3); //add stack frame used
}

int foo(int i)
  requires stk::RS<n> & i>=0
  ensures stk::RS<n> * stk_min::RS_min<m> * stk_max::RS_max<h>
       & h<=n+2*(i+1) & res=2*i;
{ 
  add_stk(2);
  mark();
  int r;
  if (i==0) r=0;
  else r=2+foo(i-1);
  sub_stk(2);
  return r;
}


void cond(int i)
  requires stk::RS<n> 
  ensures stk::RS<n> * stk_min::RS_min<m> * stk_max::RS_max<h>
       & m>=n+4 & h<=n+4 & i<0
  or stk::RS<n> * stk_min::RS_min<m> * stk_max::RS_max<h>
       & m>=n+5 & h<=n+5 & i>=0
  ;
{ 
  add_stk(2);
  mark();
  if (i<0) g();
  else h();
  sub_stk(2);
}
