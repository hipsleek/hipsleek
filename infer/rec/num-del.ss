relation B(int n, int a, int r).

int del(int n, int a)
  infer  [n,B]
  requires true
  ensures  B(n,a,res); 
{  
  if (a==1) {
    acc2(n); 
    n=n-1;
    return n;
  } else {
    acc(n);
    return 1+del(n-1,a-1);
  }
}

void acc(int n)
  requires n>=1
  ensures true;

void acc2(int n)
  requires n>=2
  ensures true;
