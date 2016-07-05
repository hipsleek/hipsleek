data node {
  int val;
  node next;
}

ll1<> == self = null
  or self::node<_, q> * q::ll1<>
  inv true;

ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n-1> 
  inv n >= 0;

relation A(int n, int m, int z).
relation B(int n, int m).
/*
infer  [n,A]
Inferred Heap:[]
Inferred Pure:[ n!=0, n!=0, n!=0, n!=0]
FIXPOINT:  m>=0 & z>=(1+m) & z=n+m
NEW RELS: [ 
m>=0 & z=m+1 & n=1 -->  A(n,m,z), 
0<=z & 0<=m & A(n-1,m,z+1) & 1<=n -->  A(n,m,z)]

infer  [n,m,A]
Inferred Pure:[ (n!=0 | m!=0) & (n!=0 | 1>m),  (n!=0 | m!=0) & (n!=0 | 1>m), (n!=0 | m!=0) & (n!=0 | 1>m), (n!=0 | m!=0) & (n!=0 | 1>m)]
NEW RELS: [ ( (m=0 & z=1 | 1<=m & -1+z=m) & n=1) -->  A(n,m,z), ( 1<=z_580 & 1+n_557=n & m_558=m & -1+z=z_580 & 0<=m & A(n_557,m_558,z_580) & 
1<=n) -->  A(n,m,z)]

P:={[n,m]:n>=0 & m>=0};
S1 := {[n,m]:(n!=0 | m!=0) & (n!=0 | 1>m)};
S2 := P intersection S1;
PairWiseCheck S1;
PairWiseCheck S2;

==> simplifies pre to n>=1 & m>=0

Main relation simplifies to:

 m>=0 & z=m+1 & n=1 -->  A(n,m,z), 
 0<=z & 0<=m & A(n-1,m,z+1) & 1<=n -->  A(n,m,z)

For precondition we get:
   A(n,m) = n=1 & m>=0
   A(n,m) = n>=1 & A(n-1,m)

   A(n,m) = n=1 & m>=0
   A(n,m,nr,mr) = n=1 & n=mr & m=mr
        \/ n>=1 & A(n,m,n-1,m)


*/

// TOCHECK why pre is too weak! when we use:
// infer [n,m,A]
// Inferred Pure:[ n!=0 | m!=0, n!=0 | m<=0, n!=0 | m!=0, n!=0 | m<=0]
// inferred pre : (n!=0 | m<=0) 

// TODO: WHY infer m>=0 when not in infer list
//!!! POST:  m>=0 & z>=(1+m) & z=n+m
//!!! PRE :  0<=m & 1<=n

void append(node x, node y)
// infer [n,m,B]
  infer [n,A]
  requires x::ll<n>*y::ll<m> //& n>=0 & m>=0
  ensures x::ll<z> & A(z,m,n);

//  requires x::ll<n>*y::ll<m> 
//  ensures x::ll<z> & A(n,m,z);
{
  if (x.next==null) {
    x.next=y; 
  } else {
    append(x.next,y);
  }
}
