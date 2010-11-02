int semiperimeter(int a, int b, int c)
requires (exists m1,m2,n1,n2,k1,k2: a = (n1/n2)*((m1*m1/(m2*m2))+k1*k1/(k2*k2)) & b = (m1/m2)*(n1*n1/(n2*n2)+k1*k1/(k2*k2)) & c = (m1/m2 +n1/n2)*(m1*n1/(m2*n2)-k1*k1/(k2*k2)))
ensures res = m1 * n1 * (m1/m2 + n1/n2)/(m2*n2);
{ return (a + b + c ) /2;
}

