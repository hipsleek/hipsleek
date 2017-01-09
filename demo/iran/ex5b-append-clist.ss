data node {
	int val;
	node next;
}

lseg<n,p> == self=p & n=0
  or self::node<_, q> * q::lseg<n-1,p> 
	inv n>=0;

clist<n> == self::node<_,p>*p::lseg<n-1,self>
  inv self!=null & n>0;

void append(node x, node y)
  requires x::lseg<n,null> & n!=0
  ensures x::lseg<n,y>;
  requires x::lseg<n,null> & n!=0 & x=y
  ensures x::clist<n>;
{
  if (x.next!=null) append(x.next, y);
  else x.next = y;
}
