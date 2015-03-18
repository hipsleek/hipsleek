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
     ensures (i>=x & r'=r &  i'=i| i<x & r'=r+2*(x-i) & i'=x+1);
  {
    i=i+1;
    r=r+2;
  }
  return r;
}


