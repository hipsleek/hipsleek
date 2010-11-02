/*

int area_p2(int a,int b,int c)
requires (exists m1,m2,n1,n2,k1,k2: a = (n1/n2)*((m1*m1/(m2*m2))+k1*k1/(k2*k2)) & b = (m1/m2)*(n1*n1/(n2*n2)+k1*k1/(k2*k2)) & c = (m1/m2 +n1/n2)*(m1*n1/(m2*n2)-k1*k1/(k2*k2)))
ensures res = ((m1*n1*k1/(m2*n2*k2))*(m1/m2+n1/n2)*(m1*n1/(m2*n2)-k1*k1/(k2*k2)))* ((m1*n1*k1/(m2*n2*k2))*(m1/m2+n1/n2)*(m1*n1/(m2*n2)-k1*k1/(k2*k2)));
{
int s;
s = (a + b +c)/2;
return s*(s-a)*(s-b)*(s-c);
}

*/

int area(int a, int b, int c, int m, int n, int k)
  requires a = n*(m*m+k*k) & b = m*(n*n+k*k) & c = (m+n)*(m*n-k*k)
  ensures res = 16*k*m*n*(m+n)*(m*n-k*k)*k*m*n*(m+n)*(m*n-k*k);
{
  int p = a+b+c;
  return p*(p-2*a)*(p-2*b)*(p-2*c);
}

int area2(int m, int n, int k)
  requires true
  ensures res = 16*k*m*n*(m+n)*(m*n-k*k)*k*m*n*(m+n)*(m*n-k*k);
{
  int a = n*(m*m+k*k);
  int b = m*(n*n+k*k);
  int c = (m+n)*(m*n-k*k);
  int p = a+b+c;
  return p*(p-2*a)*(p-2*b)*(p-2*c);
}
