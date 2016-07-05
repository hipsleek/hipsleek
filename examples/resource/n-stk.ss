data node {
  int val;
  node next;
}

ll<n> == self=null & n=0
  or self::node<_,q> * q::ll<n-1>
  inv n>=0;

pred_prim stk2<high:int>
  inv high>=0;


void check_stk(stk2 x, int n)
  requires x::stk2<a>@L & a>=n
  ensures true;

void subtr_stk(stk2 x, int n)
  requires x::stk2<a> & a>=n
  ensures x::stk2<a-n>;

int foo(stk2 x, int n) 
  requires x::stk2<3>
  ensures x::stk2<2> & res=n;
{
  check_stk(x,2);
  check_stk(x,3);
  //check_stk(x,4);
  subtr_stk(x,1);
  return n;
}

