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
  requires x::lseg<n,null> & n!=0 & Term[n]
  ensures x::lseg<n,y>;
  requires x::lseg<n,null> & n!=0 & x=y & Term[n]
  ensures x::clist<n>;
{
  if (x.next!=null) append(x.next, y);
  else x.next = y;
}

/*

# ex5d-bug

 Why is there is non-decreasing issue?
 Seems like another multi pre/post issue..

Termination checking result: 
(15)->(19) (MayTerm ERR: not decreasing)  Term[7; 0; n] ->  Term[7; 1; n_1595]

*/
