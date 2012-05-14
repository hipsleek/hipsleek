/* doubly linked lists */

/* representation of a node */
data node2 {
	int val; 
	node2 prev;
	node2 next;	
}

/* view for a doubly linked list with size */
dll<p,n> == self = null & n = 0 
  or self::node2<_ ,p , q> * q::dll<self, n-1> // = q1 
	inv n >= 0;


relation D(int x, int y, int z, node2 m, node2 n, node2 p).

void append2(node2 x, node2 y)
  infer  [m,D]
	requires x::dll<q, m> * y::dll<p, n>
	ensures x::dll<r, t> & D(t,m,n,r,p,q);

{
	node2 tmp;


	if (x.next == null) {
		x.next = y;
		if (y != null) {
			y.prev = x;
		}		
	}
	else {
		append2(x.next, y);
	}
}

/*

// TODO post should be t=m+n 

Checking procedure append2$node2~node2... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ m!=0, m!=0, m!=0]
!!! REL :  D(t,m,n,r,p,q)
!!! POST:  n>=0 & 1=m & q=r & n+1=t
!!! PRE :  m=1 & 0<=n
!!! NEW RELS:[ (m=1 & n=0 & r=q & t=1) --> D(t,m,n,r,p,q),
 (exists(flted_12_828:(t=2 & n=1 | 2+flted_12_828=t & 1+n=t & 3<=t) & r=q & 
  m=1)) --> D(t,m,n,r,p,q),
 (m=1 & n=0 & r=q & t=1) --> D(t,m,n,r,p,q)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
*/
