data node {
	int val;
	node next;
}

ll<n> == self=null & n=0
	or self::node<_, q> * q::ll<n-1>
	inv n>=0;

lseg<n,p> == self=p & n=0
  or self::node<_, q> * q::lseg<n-1,p> 
	inv n>=0;

clist<n> == self::node<_,p>*p::lseg<n-1,self>
  inv self!=null & n>0;

lemma_unsafe self::clist<n> <- self::lseg<n-1,q>*q::node<_,self>;

void append(node x, node y)
  requires x::ll<n> * y::ll<m> & n!=0 & Term[n]
  ensures x::ll<n+m>;
  requires x::lseg<n,null> & n!=0 & Term[n]
  ensures x::lseg<n,y>;
  requires x::lseg<n,null> & n!=0 & x=y & Term[n]
  ensures x::clist<n>;
  requires x::clist<n> & Loop ensures false;
{
  if (x.next==null) x.next = y;
  else append(x.next, y);
}

