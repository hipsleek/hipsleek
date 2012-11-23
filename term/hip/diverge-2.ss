

void loop2(ref int x, ref int n, int N)
 requires n>=0 & x>=1 & 1<N<1000
  case {
  x<=N -> requires Term[N-x] ensures true; //x'>=2 & x'>x;
  x>N -> requires Term[] ensures true; //x'=x; //'
  }
{
  if (x<=N) {
    n = n+1;
    x = n*x;
    loop2(x,n,N);
    }
}


void loop(ref int x, int y)
 requires x>2
  case {
  x<y -> requires Term[y-x] ensures true; //x'>=2 & x'>x;
  x>=y -> requires Term[] ensures true; //x'=x; //'
  }
{
  if (x<y) {
    x = pow3(x)-2*pow2(x) - x+2;
    loop(x,y);
    }
}

int pow2(int x)
  requires Term[]
  ensures res = x*x;
{
  return x*x;
}


int pow3(int x)
  requires Term[]
  ensures res = x*x*x;
{
  return x*x*x;
}
