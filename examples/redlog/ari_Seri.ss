int ari_series(int a1, int n, int d)
requires n>0 
ensures res = n * (2 * a1 + d * (n - 1)) / 2;
{
 
 return n * (2 * a1 + (n - 1) * d) / 2;
}
int ari2(int a1, int a2, int d,int n)
requires d != 0 &  n>=0 & ( a2 - a1 ) = d *n
ensures res = ((a2 - a1)/ d +1)*(a2 + a1) /2;
{
  int t = (a2 - a1) / d;
  return (t + 1) * (a1 + a2) / 2;
}

int ari3(int a, int d, int m)
requires m>=0 
ensures res= m*(3*a+d*(m-1))/2;
{ 
  if (m==0) return 0;
  else return a+ari3(a+d,d,m-1);
}

int ari4(int a1, int a2, int d, int m)

/*
requires m>=0 & a2-a1 = m*d & d!=0
ensures res= ((m+1)*(2*a1+d*m))/2;
requires d=0 & a2!=a1
ensures false;
requires d=0 & a2=a1
ensures res=a1; */
 case {
  d=0 -> case {
    a2=a1 -> ensures res=a1;
    a2!=a1 -> ensures false; }
  d!=0 -> requires m>=0 & a2-a1 = m*d & d!=0 
          ensures res= ((m+1)*(2*a1+d*m))/2;
 }
 case {
   m<0 -> requires false ensures false; //requires a2-a1=m*d ensures false;
   //m>=0 -> requires true ensures true; 
   //m=0 -> requires a2=a1 & d!=0 ensures res=a1;
   m>=0 -> requires a2-a1=m*d & d!=0 ensures res=((m+1)*(2*a1+d*m))/2;
   //m>0 -> requires true ensures true;
 }
{ 
  if (a2==a1) return a1;
  else return a1+ari4(a1+d,a2,d,m-1);
}


int ari5(int a1, int a2, int d, int m)
requires m>=0 & a2-a1 = m*d //& d!=0
ensures res= ((m+1)*(2*a1+d*m))/2;
//requires d=0 & a2!=a1
//ensures false;
//requires d=0 & a2=a1
//ensures res=a1;
{ 
  if (m==0) return a1;
  else return a1+ari5(a1+d,a2,d,m-1);
}

/* requires [m] true & a2-a1=m*d */
