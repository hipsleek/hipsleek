relation R(int a, int b).
relation R1(int a, int b).
relation R2(int a, int b, int c).
relation R3(int a).
relation R4(int a, int b).

data node {
  int val;
  node next;
}

ll<n> == self = null & n = 0
  or self::node<_, q> * q::ll<n-1>
  inv n >= 0;
/*
int length(node x)
 infer [@post_n]
  requires x::ll<n> ensures x::ll<m>  ;
{
  if (x==null) return 0;
  else return 1+length(x.next);
}

int length1(node x)
  infer [@pre_n,@post_n]
  requires x::ll<n> ensures x::ll<m>  ;
{
  if (x==null) return 0;
  else return 1+length1(x.next);
}

int length2(node x)
  infer [R,@post_n]
  requires x::ll<n> & R(n,m)
  ensures x::ll<m>;
{
  if (x==null) return 0;
  else return 1+length2(x.next);
}
*/

int length3(node x)
  infer [R1,R2]
  requires x::ll<n> & R1(n,m)
  ensures x::ll<m> & R2(n,m,res);
{
  if (x==null) return 0;
  else return 1+length3(x.next);
}

int length4(node x)
  infer [R1,R2]
  requires x::ll<n>
  ensures x::ll<m> & R2(n,m,res);
{
  if (x==null) return 0;
  else return 1+length4(x.next);
}
