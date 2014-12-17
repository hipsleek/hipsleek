
relation P(int n).
relation Q(int n,int r).


int id(int n)

  infer [@post_n,@term]
  requires true ensures true;
/*
 case {
   n<=0 -> requires Loop ensures false;
   n>0 -> requires Term[n+2] ensures res=2*n;
 }
*/
{
  if (n==0) return 0;
  else return 2+id(n-1);
}

/*
# sim3a

This example does not work with @post_n
because we derived:

    ensures res=2*n & n>=0



 */
