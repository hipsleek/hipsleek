data node {
	int val;
	node next;
}

data node2 {
	int val;
	node2 prev;
	node2 next;
}

dll<n,p> == self=null & n=0
	or self::node2<_,pr,q> * q::dll<n-1,self> & p=pr 
	inv n>=0;

list<> == self=null
        or self::node<_, q> * q::list<>
        inv true;

ll<n> == self=null & n=0
	or self::node<_, q> * q::ll<n-1>
	inv n>=0;

void append2(node2 x, node2 y)
	requires x::dll<n,np> * y::dll<m,_> & n>0 
	 ensures x::dll<n+m,np>;
{
   if (x.next!=null) {
     	append2(x.next,y); return;
  } else {
		x.next = y;
		if (y!=null) y.prev=x;
		return;
	}
}
	
void append(node x, node y)
	requires x::list<> * y::list<> & x!=null 
	ensures x::list<>;
	requires x::ll<n> * y::ll<m> & n>0
	 ensures x::ll<n+m>;
{
	if (x.next != null) {
		append(x.next,y);
		return;
	}
	else {
		x.next = y;
		return;
	}
}

