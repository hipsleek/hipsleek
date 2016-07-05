// this is now to specify the min stack required
// by a given method; it is specified in the post-condition

pred_prim RS<low:int>
  inv low>=0;

pred_prim RS_min<low:int>
  inv low>=0;

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
  ensures stk_min::RS_min<a>;

bool rand()
 requires true
 ensures res or !res;


void f() 
  requires stk::RS<n>
  ensures  stk::RS<n> * stk_min::RS_min<m> & m>=n+5;
{
  add_stk(2); //add stack frame used
  mark();
  g(); h();
  //h(); g();
  //dprint;
  sub_stk(2); //add stack frame used
}


void g() 
  requires stk::RS<n> 
  ensures  stk::RS<n> * stk_min::RS_min<m> & m>=n+2;
{
  add_stk(2); //add stack frame used
  mark();
  sub_stk(2); //add stack frame used
}

void h() 
  requires stk::RS<n> 
  ensures  stk::RS<n> * stk_min::RS_min<m> & m>=n+3;
{
  add_stk(3); //add stack frame used
  mark();
  sub_stk(3); //add stack frame used
}

