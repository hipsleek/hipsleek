relation facta(int n, int f).
axiom n=0 ==> facta(n,1).
axiom n > 0 & facta(n-1,f1) ==> facta(n,n*f1).

// Add a strongest precondition using facta relation
// to prove functional correctness of fact function below.

int fact(int n)
  requires n>=0
  ensures res>0;
{
  if (n==0) return 1;
  else return n*fact(n-1); 
}

