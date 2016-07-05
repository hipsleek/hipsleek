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
/*
  requires x::lseg<n,null> & n!=0 & Term[n]
  ensures x::lseg<n,y>;
*/
  requires x::clist<n> & Loop
  ensures true;
{
  if (x.next==null) x.next = y;
  else append(x.next, y);
}

/*
# ex5g-bug

 Why is false post-cond not being checked
 for Loop? There is also no message indicating
 that term-checking is being done.

  requires x::clist<n> & Loop
  ensures true;

Checking procedure append$node~node... 
Procedure append$node~node SUCCESS.


*/
