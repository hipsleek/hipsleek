// this is now to specify the min stack required
// by a given method; it is specified in the post-condition

pred_prim RS<low:int>
  inv low>=0;

global RS stk_min;

// add back space into stack
void add_min(int n)
  requires stk_min::RS<a> & n>=0
  ensures stk_min::RS<a+n>;

void sub_min(int n)
  requires stk_min::RS<a> & a>=n & n>=0
  ensures stk_min::RS<a-n>;

bool rand()
 requires true
 ensures res or !res;

void f() 
  requires stk_min::RS<n>
  ensures  stk_min::RS<m> & m-n>=4;
{
  add_min(2); //add stack frame used
  //dprint;
  if (rand()) g();
  else h();
}

void g() 
  requires stk_min::RS<n> 
  ensures  stk_min::RS<m> & m-n>=2;
{
  add_min(2); //add stack frame used
}

void h() 
  requires stk_min::RS<n> 
  ensures  stk_min::RS<m> & m-n>=3;
{
  add_min(3); //add stack frame used
}
