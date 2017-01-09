data node {
	int val;
	node next;
}

lseg<n,p> == self=p & n=0
  or self::node<_, q> * q::lseg<n-1,p> 
	inv n>=0;

clist<n> == self::node<_,p>*p::lseg<n-1,self>
  inv self!=null & n>0;

lemma_unsafe self::clist<n> <- self::lseg<n-1,q>*q::node<_,x>;

void append(node x, node y)
  requires x::clist<n> & Loop
  ensures true;
{
  if (x.next==null) x.next = y;
  else append(x.next, y);
}

