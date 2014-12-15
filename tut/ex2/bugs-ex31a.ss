data node {
  int val;
  node next;
}

/*
ll<n> == emp & self=null & n=0
  or self::node<_,q>*q::ll<n-1>
  inv n>=0;
*/

ls_nt<p> == emp & self=p
  or self::node<_,q>*q::ls_nt<p> & self!=p
  inv true;

cll<> == self::node<_,q>*q::ls_nt<self> 
  inv self!=null;



int length(node x,node p)
  requires x::ls_nt<p>
  ensures x::ls_nt<p>;

int len_cll(node x)
  requires x::cll<>
  ensures x::cll<> & res>0;
{
  node n=x.next;
  return 1+length(n,x);
}

