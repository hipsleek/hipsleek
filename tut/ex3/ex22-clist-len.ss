data node {
  int val;
  node next;
}

ll<> == emp & self=null
  or self::node<_,q>*q::ll<>
  inv true;

/* non-touching list segment */
ls_nt<p> == emp & self=p
  or self::node<_,q>*q::ls_nt<p> & self!=p
  inv true;

/* circular list */
cll<> == self::node<_,q>*q::ls_nt<self> 
  inv self!=null;


int len_cll(node x)
  requires x::cll<>
  ensures x::cll<> & res>0;
{
  node n=x.next;
  return 1+length(n,x);
}


int length(node x,node p)
 case {
  x=p -> ensures emp & res=0;
  x!=p -> requires x::ls_nt<p>
          ensures x::ls_nt<p> & res>0;
  }
{
  if (x==p) return 0;
  else return 1+length(x.next,p);
}


