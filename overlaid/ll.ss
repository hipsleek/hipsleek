/* singly linked lists */

/* representation of a node */

data node {
	int val; 
	node prev;	
	node next;	
}


/* view for a doubly linked list */

dll<n,pr,l,last> == n = 0 & self=l & pr=last 
  or self::node<_, pr,l> & self=last & n=1
  or self::node<_, pr,q> * q::dll<n-1,self,l,last> & q!=null
  inv n >= 0;

// x::dll<n,pr,l,last> & n>0 <==> x::dll<n-1,pr,last,pp> * last::node<_,pp,l>

ll<n,l> == n = 0 & self=l 
  or self::node<_, _,q> * q::ll<n-1,l> 
  inv n >= 0;

lr<n,pr> == n = 0 & self=pr 
  or self::node<_, p,_> * p::lr<n-1,pr> 
  inv n >= 0;

node delete_first(node x)
  requires x::dll<n,null,null,last> & n>0
  ensures res::dll<n-1,null,null,_> * x::node<_,_,_> ;
{
  node nx;
  nx = x.next;
  if (nx==null) {
    return nx;
  } else {
    dprint;
    nx.prev=null;
    return nx;
  }
}




