// use "hip -tp redlog"
// Add a weakest precondition that ensures
// that method below goes into an infinite Loop!

int fact(int n)
  requires Loop 
  ensures false;
{
  if (n==0) return 1;
  else return n*fact(n-1); 
}

