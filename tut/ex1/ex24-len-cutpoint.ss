data node {
  int val;
  node next;
}

ll<n> == emp & self=null & n=0
  or self::node<_,q>*q::ll<n-1>
  inv n>=0;

int length(node x)
  requires x::ll<n>@L
  ensures res=n;

int length_old(node x)
  requires x::ll<n>
  ensures x::ll<n> & res=n;

int foo(ref node y)
  requires y::ll<m>
  ensures y'::ll<m+1> & res=3+m+1; //'
{
  y = new node(3,y);
  int ln = length(y);
  //int ln = length_old(y);
  return ln+y.val;
}

/*
  Exercise: What would be a better spec for foo?


*/



