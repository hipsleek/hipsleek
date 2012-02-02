data node {
  int val;
  node next;
}

ranking r1(int n).
ranking r2(int n).

ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n-1> 
  inv n >= 0;

void append(node x, node y)
  infer [r1,r2]
  requires x::ll<n>*y::ll<m> & n>0 & Term[r1(n)]
  ensures x::ll<z> & z=m+n;
{
  app2(x,y);
}

void app2(node x, node y)
  infer [r1,r2]
  requires x::ll<n>*y::ll<m> & x!=null & Term[r2(n)]
  ensures x::ll<z> & z=m+n;
{
  if (x.next==null) {
    x.next=y; 
  } else {
    append(x.next,y);
  }
}


/*

Bounded
=======
( 1<=n) -->  (r1(n))>=0, 
( 1<=n) -->  (r2(n))>=0, 
1. r1[1]>=1; r2[1]>=1

Decreasing
==========
( n=n_590 & 1<=n_590) -->  (r1(n))>(r2(n_590))]
( n_637=n - 1 & 2<=n) -->  (r2(n))>(r1(n_637))]

1. r1[1]->r2[1]:NC
2. r2[1]->r1[1]:DEC(1)


*/

