data node {
  int val;
  node next;
}

ll<n> == emp & self=null & n=0
  or self::node<_,q>*q::ll<n-1>
  inv n>=0;

/* non-touching list segment */
ls<n,p> == emp & self=p & n=0
  or self::node<_,q>*q::ls<n-1,p> 
  inv n>=0;

/* circular list */
cll<n> == self::node<_,q>*q::ls<n-1,self> 
  inv self!=null & n>0;


int len_cll(node x)
  requires x::cll<n> & Term
  ensures x::cll<n> & res=n;
{
  node n=x.next;
  return 1+length(n,x);
}


int length(node x,node p)
 case {
  x=p -> requires Term ensures emp & res=0;
  x!=p -> requires x::ls<n,p> & Term[n]
          ensures x::ls<n,p> & res=n;
  }
{
  if (x==p) return 0;
  else return 1+length(x.next,p);
}


