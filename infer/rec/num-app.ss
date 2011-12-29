relation A(int n, int m, int z).

int appN(int n, int m)
  infer @pre [n,m,A]
  requires n>=0
  ensures A(n,m,res);
{
  nonnull(n);
  if (n==1) {
    return m+1; 
  } else {
    return 1+appN(n-1,m);
  }
}

void nonnull(int n)
  requires n>=1
  ensures true;
