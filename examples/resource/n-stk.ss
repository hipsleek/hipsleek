data cell {
  int val;
}

stk<high:int> == self::cell<high> & high>=0 
  inv high>=0;

pred_prim stk<high:int>
  inv high>=0;

int foo(int n) 
  requires true
  ensures res=n+1;
{
  n =n+1;
  return n;
}

