/* LDK
 * Return integral square root of an integer n
 * Need "-tp redlog" to handle multiplication
 */

int ISqrt(int n) 
  requires n>=0
  ensures res*res <=n & n<(res+1)*(res+1);
{
 int x = 0;
 while ((x+1)*(x+1) <= n)

  requires n>=0 &  x*x <=n
  ensures x'*x' <=n & n<(x'+1)*(x'+1);
 //inv x*x <=n

 /* case{ */
 /*   n>=0 -> */
 /*     requires x*x <=n */
 /*     ensures x'*x' <=n & n<(x'+1)*(x'+1); */
 /*     //inv x*x <=n */

 /*   n<0 -> ensures x'=x; */
 /* } //' */

  {
    x = x+1;
  }
 return x;
}

void main()
{
  int t = ISqrt(4);
  //int t=2;
  assert t'=2;
}
