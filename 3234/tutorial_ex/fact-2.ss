// Add a weakest precondition over [n] that ensures
// that fact will terminate.
// Instead of 2*n as the ranking function,
// use a smaller ranking one, if possible.

int fact(int n)
  requires true & Term[2*n]
  ensures res>0;
{
  if (n==0) return 1;
  else return n*fact(n-1); 
}

