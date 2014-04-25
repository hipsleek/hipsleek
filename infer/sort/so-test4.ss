data node {
	int val; 
	node next; 
}

llN<n> == self=null & n=0
  or self::node<_, p> * p::llN<n-1>
inv n>=0;

llH<v, R:relation(int,int)> == self::node<v, null>
  or self::node<v, q> * q::llH<w, R> & R(v, w)
  inv true;

relation P(int a, int b).
relation Q(int a, int b, int c).

relation P1(int a, int b).
relation Q1(int a, int b, int c).

node zip(node x, node y)
  infer [Q]
  requires x::llN<a> * y::llN<b> /* & P(a,b) */ & b>=a & a>=0
  ensures  res::llN<r> & Q(r,a,b);
{
  if (x==null) return null;
    else{
           x.val=x.val+y.val;
           x.next=zip(x.next, y.next);
           return x;
    }
}

