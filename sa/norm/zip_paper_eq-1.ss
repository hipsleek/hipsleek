data node{
	int val;
	node next;
}

ll<n> == self = null & n=0  or self::node<_, q> * q::ll<n-1>
inv n>=0;

  relation P(int a, int b).
  relation Q(int a, int b, int c).


node zip (node x, node y)
infer [P,Q]  
requires x::ll<n>@L*y::ll<m>@L & P(m,n) 
ensures res::ll<k> & Q(m,n,k);
/*
requires x::ll<n>@L*y::ll<m>@L & n<=m 
ensures res::ll<k> & k=m;
*/
{
  if (x==null) 
    {
      if (y==null) return null;
      else 
        {
          assert false assume false; 
          return x;
        }
    }
  else {
    /*
    if (y==null) { 
       assert false;
       return y;
    } else
    */
    return new node(x.val+y.val, zip(x.next,y.next));
  }
}

/*

Correctly inferred pre/post pure relation:

!!! pure pre: m=n & 0<=m
*************************************
*******fixcalc of pure relation *******
*************************************
[( Q(m,n,k), k=m & k=n & 0<=k, P(m,n), m=n)]
*************************************

!!!REL POST :  Q(m,n,k)
!!!POST:  k=m & k=n & 0<=k
!!!REL PRE :  P(m,n)
!!!PRE :  m=n

*/

