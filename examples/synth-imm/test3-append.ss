data node {
	int val;
	node next;
}

lseg<p, n> == self=p & n=0
	or self::node<_, r> * r::lseg<p, n-1> //& self!=p
	inv n>=0;

void append(node x, node y)
     requires x::lseg<null,n1> * y::lseg<z,n2> & x!=null
     ensures  x::lseg<z,n1+n2>;
{
  if(x.next == null) x.next = y;
  else append(x.next,y);
}
