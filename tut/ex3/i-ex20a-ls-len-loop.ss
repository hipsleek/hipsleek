data node {
  int val;
  node next;
}

ls<n, p> ==
 case {
  n=0 -> [] emp & self = p & n = 0;
  n!=0 -> [] self::node<_,q>*q::ls<n-1,p>;
} inv n >= 0;

/*
nt_ls<n,p> == emp & self=p & n=0
  or self::node<_,q>*q::nt_ls<n-1,p> & self!=p
  inv n>=0;
*/

clist<n> == self::node<_,q>*q::ls<n-1,self>
  inv n>0;

lemma_unsafe self::clist<n> <- self::ls<n-1,q> * q::node<_,self>;

int length(node x)
  infer[@term]
  requires x::clist<n>
  ensures true;
{
  if (x==null) return 0;
  else return 1+length(x.next);
}

