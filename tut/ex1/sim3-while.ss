// pass-by-value parameter x
// x' is the current value of variable x
// x  is orig value at start of method


int foo(int x)
  requires x>0
  ensures res=2*(x-1);
{
  int i=1;
  int r=0;
  while (i<x) 
     requires true
     ensures (i>=x & r'=r | i<x & r'=r+2*(x-i));
  {
    i=i+1;
    r=r+2;
  }
  return r;
}

/*
# sim4-while.ss

  Can we omit this message since __norm is allowable.

  WARNING: sim4-while.ss_14:13_14:47:the result type __norm#E is not 
  covered by the throw list[__Brk_top#E]
*/
