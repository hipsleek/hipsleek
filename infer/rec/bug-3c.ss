data node {
  int val;
  node next;
}

ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n-1> 
  inv n >= 0;

relation A(int n, int m, int z).


// TODO why pre is too weak! when we use:
// infer [n,m,A]
// why did we infer below:
// Inferred Pure:[ n!=0 | m!=0, n!=0 | m<=0, n!=0 | m!=0, n!=0 | m<=0]
// inferred pre : (n!=0 | m<=0)
// These are two weak. Why did we have m<=0?
// Did we not use xpure0?

void append(node x, node y)
  //infer [n,m,A]
  infer [n,m,A]
  requires x::ll<n>*y::ll<m> & n>=0 & m>=0
  ensures x::ll<z> & A(n,m,z);

//  requires x::ll<n>*y::ll<m> 
//  ensures x::ll<z> & A(n,m,z);
{
  if (x.next==null) {
    x.next=y; 
  } else {
    append(x.next,y);
  }
}
