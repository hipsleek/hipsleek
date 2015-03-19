/* Size Property */
data node {
  int val;
  node next;
}

ll<> == self = null
  or self::node<_, q> * q::ll<>
  inv true;

llN<n> == self = null & n=0
  or self::node<_, q> * q::llN<n-1>
  inv n>=0;

/*
TODO: make it work with --eps for below

void append(node x, node y)
  infer {ll->llN} []
  requires x::ll<> * y::ll<> & x!=null
  ensures x::ll<>;
{
  if (x.next == null)
    x.next = y;
  else
    append(x.next, y);
}

relation R1(int a, int b).
relation R2(int a, int b, int c).
void append1(node x, node y)
/*  infer [R1,R2]*/
  requires x::llN<n> * y::llN<m> & x!=null //& R1(n,m)
  ensures x::llN<z> & z=n+m;//& R2(n,m,z);
{
  if (x.next == null)
    x.next = y;
  else
    append1(x.next, y);
}

*/

relation R1(int a, int b).
relation R2(int a, int b, int c).
void append1(node x, node y)
  infer [R1,R2]
  requires x::llN<n> * y::llN<m> & x!=null & R1(n,m)
  ensures x::llN<z> & R2(n,m,z);
{
  if (x.next == null)
    x.next = y;
  else
    append1(x.next, y);
}

relation R3(int a,int b,int c).
int retmax(int a,int b)
infer [R3]
requires true
ensures R3(res,a,b);
{
if (a>b) return a;
else return b;
}
