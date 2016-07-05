relation A(int n, int m, int z).

int appN(int n, int m)
  infer [n,m,A]
  requires true
  ensures A(n,m,res);
{
  acc(n);
  if (n==1) {
    return m+1; 
  } else {
    return 1+appN(n-1,m);
  }
}

void acc(int n)
  requires n>=1
  ensures true;
