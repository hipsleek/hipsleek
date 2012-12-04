data stk2 {
  int val;
}

pred_prim stk2<high:int>
  inv high>=0;

void check_stk(stk2 x, int n)
  requires x::stk2<a>@L & a>=n
  ensures true;

int foo(stk2 x, int n) 
  requires x::stk2<3>
  ensures x::stk2<2> & res=n;
{
  check_stk(x,2);
  check_stk(x,3);
  //check_stk(x,4);
  return n;
}

