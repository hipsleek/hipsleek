data node {
  int val;
  node next;
}

ll<n> == emp & self=null & n=0
  or self::node<_,q>*q::ll<n-1>
  inv n>=0;

node gen_inf(int n)
  requires true
  ensures res::ll<m>;

{
  node t = new node(n,null);
  t.next = gen_inf(n+1);
  return t;
}

